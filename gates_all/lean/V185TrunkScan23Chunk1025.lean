import V185TrunkScan23Chunk1024

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6068450 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6068450 : Nat := 118140960795 + 6068450 * 2 ^ 59
def prefixEnd_6068450 : Nat := 4983230072969 + 3 ^ 40 * 6068450 * 2
def baseEnd_6068450 : Nat := 3116031677776887395166713

theorem tailTrace_6068450 : CollatzResearch.WordTrace tailWord_6068450 prefixEnd_6068450 3116031677776887395166713 := by
  unfold tailWord_6068450
  simp only [CollatzResearch.WordTrace]
  refine ⟨55333638716262383398098701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147556369910033022394929869 55333638716262383398098701)
  ·
    refine ⟨20750114518598393774287013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55333638716262383398098701 20750114518598393774287013)
    ·
      refine ⟨3890646472237198832678815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20750114518598393774287013 3890646472237198832678815)
      ·
        refine ⟨5835969708355798249018223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3890646472237198832678815 5835969708355798249018223)
        ·
          refine ⟨8753954562533697373527335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5835969708355798249018223 8753954562533697373527335)
          ·
            refine ⟨13130931843800546060291003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8753954562533697373527335 13130931843800546060291003)
            ·
              refine ⟨19696397765700819090436505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13130931843800546060291003 19696397765700819090436505)
              ·
                refine ⟨14772298324275614317827379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19696397765700819090436505 14772298324275614317827379)
                ·
                  refine ⟨22158447486413421476741069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14772298324275614317827379 22158447486413421476741069)
                  ·
                    refine ⟨8309417807405033053777901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22158447486413421476741069 8309417807405033053777901)
                    ·
                      refine ⟨3116031677776887395166713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8309417807405033053777901 3116031677776887395166713)
                      ·
                        rfl

theorem cell23_6068450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6068450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068450 prefixEnd_6068450 := by exact prefixLift 6068450
  have htrace : WordTrace (prefixWord ++ tailWord_6068450) baseStart_6068450 baseEnd_6068450 := by
    simpa [prefixWord, tailWord_6068450, baseEnd_6068450] using wordTrace_append hprefix tailTrace_6068450
  have hstable : (prefixWord ++ tailWord_6068450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068450).length < 2 ^ (prefixWord ++ tailWord_6068450).sum := by decide
  have hdescent : baseEnd_6068450 < baseStart_6068450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068452 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_6068452 : Nat := 118140960795 + 6068452 * 2 ^ 59
def prefixEnd_6068452 : Nat := 4983230072969 + 3 ^ 40 * 6068452 * 2
def baseEnd_6068452 : Nat := 3116032704738196387341703

theorem tailTrace_6068452 : CollatzResearch.WordTrace tailWord_6068452 prefixEnd_6068452 3116032704738196387341703 := by
  unfold tailWord_6068452
  simp only [CollatzResearch.WordTrace]
  refine ⟨110667313905521143966983805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147556418540694858622645073 110667313905521143966983805)
  ·
    refine ⟨41500242714570428987618927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110667313905521143966983805 41500242714570428987618927)
    ·
      refine ⟨62250364071855643481428391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41500242714570428987618927 62250364071855643481428391)
      ·
        refine ⟨93375546107783465222142587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62250364071855643481428391 93375546107783465222142587)
        ·
          refine ⟨140063319161675197833213881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93375546107783465222142587 140063319161675197833213881)
          ·
            refine ⟨105047489371256398374910411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140063319161675197833213881 105047489371256398374910411)
            ·
              refine ⟨157571234056884597562365617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105047489371256398374910411 157571234056884597562365617)
              ·
                refine ⟨118178425542663448171774213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157571234056884597562365617 118178425542663448171774213)
                ·
                  refine ⟨22158454789249396532207665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118178425542663448171774213 22158454789249396532207665)
                  ·
                    refine ⟨16618841091937047399155749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22158454789249396532207665 16618841091937047399155749)
                    ·
                      refine ⟨3116032704738196387341703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16618841091937047399155749 3116032704738196387341703)
                      ·
                        rfl

theorem cell23_6068452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_6068452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068452 prefixEnd_6068452 := by exact prefixLift 6068452
  have htrace : WordTrace (prefixWord ++ tailWord_6068452) baseStart_6068452 baseEnd_6068452 := by
    simpa [prefixWord, tailWord_6068452, baseEnd_6068452] using wordTrace_append hprefix tailTrace_6068452
  have hstable : (prefixWord ++ tailWord_6068452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068452).length < 2 ^ (prefixWord ++ tailWord_6068452).sum := by decide
  have hdescent : baseEnd_6068452 < baseStart_6068452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068456 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_6068456 : Nat := 118140960795 + 6068456 * 2 ^ 59
def prefixEnd_6068456 : Nat := 4983230072969 + 3 ^ 40 * 6068456 * 2
def baseEnd_6068456 : Nat := 3116034758660814371691685

theorem tailTrace_6068456 : CollatzResearch.WordTrace tailWord_6068456 prefixEnd_6068456 3116034758660814371691685 := by
  unfold tailWord_6068456
  simp only [CollatzResearch.WordTrace]
  refine ⟨110667386851513898308556611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147556515802018531078075481 110667386851513898308556611)
  ·
    refine ⟨166001080277270847462834917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110667386851513898308556611 166001080277270847462834917)
    ·
      refine ⟨31125202551988283899281547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166001080277270847462834917 31125202551988283899281547)
      ·
        refine ⟨46687803827982425848922321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31125202551988283899281547 46687803827982425848922321)
        ·
          refine ⟨35015852870986819386691741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46687803827982425848922321 35015852870986819386691741)
          ·
            refine ⟨13130944826620057270009403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35015852870986819386691741 13130944826620057270009403)
            ·
              refine ⟨19696417239930085905014105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13130944826620057270009403 19696417239930085905014105)
              ·
                refine ⟨14772312929947564428760579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19696417239930085905014105 14772312929947564428760579)
                ·
                  refine ⟨22158469394921346643140869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14772312929947564428760579 22158469394921346643140869)
                  ·
                    refine ⟨4154713011547752495588913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22158469394921346643140869 4154713011547752495588913)
                    ·
                      refine ⟨3116034758660814371691685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154713011547752495588913 3116034758660814371691685)
                      ·
                        rfl

theorem cell23_6068456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_6068456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068456 prefixEnd_6068456 := by exact prefixLift 6068456
  have htrace : WordTrace (prefixWord ++ tailWord_6068456) baseStart_6068456 baseEnd_6068456 := by
    simpa [prefixWord, tailWord_6068456, baseEnd_6068456] using wordTrace_append hprefix tailTrace_6068456
  have hstable : (prefixWord ++ tailWord_6068456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068456).length < 2 ^ (prefixWord ++ tailWord_6068456).sum := by decide
  have hdescent : baseEnd_6068456 < baseStart_6068456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068472 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_6068472 : Nat := 118140960795 + 6068472 * 2 ^ 59
def prefixEnd_6068472 : Nat := 4983230072969 + 3 ^ 40 * 6068472 * 2
def baseEnd_6068472 : Nat := 3116042974351286309091611

theorem tailTrace_6068472 : CollatzResearch.WordTrace tailWord_6068472 prefixEnd_6068472 3116042974351286309091611 := by
  unfold tailWord_6068472
  simp only [CollatzResearch.WordTrace]
  refine ⟨110667678635484915674847835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147556904847313220899797113 110667678635484915674847835)
  ·
    refine ⟨166001517953227373512271753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110667678635484915674847835 166001517953227373512271753)
    ·
      refine ⟨124501138464920530134203815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166001517953227373512271753 124501138464920530134203815)
      ·
        refine ⟨186751707697380795201305723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124501138464920530134203815 186751707697380795201305723)
        ·
          refine ⟨280127561546071192801958585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186751707697380795201305723 280127561546071192801958585)
          ·
            refine ⟨210095671159553394601468939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280127561546071192801958585 210095671159553394601468939)
            ·
              refine ⟨315143506739330091902203409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210095671159553394601468939 315143506739330091902203409)
              ·
                refine ⟨236357630054497568926652557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315143506739330091902203409 236357630054497568926652557)
                ·
                  refine ⟨88634111270436588347494709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236357630054497568926652557 88634111270436588347494709)
                  ·
                    refine ⟨8309447931603430157577629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88634111270436588347494709 8309447931603430157577629)
                    ·
                      refine ⟨3116042974351286309091611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8309447931603430157577629 3116042974351286309091611)
                      ·
                        rfl

theorem cell23_6068472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_6068472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068472 prefixEnd_6068472 := by exact prefixLift 6068472
  have htrace : WordTrace (prefixWord ++ tailWord_6068472) baseStart_6068472 baseEnd_6068472 := by
    simpa [prefixWord, tailWord_6068472, baseEnd_6068472] using wordTrace_append hprefix tailTrace_6068472
  have hstable : (prefixWord ++ tailWord_6068472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068472).length < 2 ^ (prefixWord ++ tailWord_6068472).sum := by decide
  have hdescent : baseEnd_6068472 < baseStart_6068472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068479 : List Nat := [1, 1, 2, 2, 1, 4, 3, 4, 5]
def baseStart_6068479 : Nat := 118140960795 + 6068479 * 2 ^ 59
def prefixEnd_6068479 : Nat := 4983230072969 + 3 ^ 40 * 6068479 * 2
def baseEnd_6068479 : Nat := 346227396523985309078231

theorem tailTrace_6068479 : CollatzResearch.WordTrace tailWord_6068479 prefixEnd_6068479 346227396523985309078231 := by
  unfold tailWord_6068479
  simp only [CollatzResearch.WordTrace]
  refine ⟨221335612581944471545200491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147557075054629647696800327 221335612581944471545200491)
  ·
    refine ⟨332003418872916707317800737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221335612581944471545200491 332003418872916707317800737)
    ·
      refine ⟨249002564154687530488350553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332003418872916707317800737 249002564154687530488350553)
      ·
        refine ⟨186751923116015647866262915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249002564154687530488350553 186751923116015647866262915)
        ·
          refine ⟨280127884674023471799394373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186751923116015647866262915 280127884674023471799394373)
          ·
            refine ⟨52523978376379400962386445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280127884674023471799394373 52523978376379400962386445)
            ·
              refine ⟨19696491891142275360894917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52523978376379400962386445 19696491891142275360894917)
              ·
                refine ⟨3693092229589176630167797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19696491891142275360894917 3693092229589176630167797)
                ·
                  refine ⟨346227396523985309078231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3693092229589176630167797 346227396523985309078231)
                  ·
                    rfl

theorem cell23_6068479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 5].length) (baseStart_6068479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068479 prefixEnd_6068479 := by exact prefixLift 6068479
  have htrace : WordTrace (prefixWord ++ tailWord_6068479) baseStart_6068479 baseEnd_6068479 := by
    simpa [prefixWord, tailWord_6068479, baseEnd_6068479] using wordTrace_append hprefix tailTrace_6068479
  have hstable : (prefixWord ++ tailWord_6068479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068479).length < 2 ^ (prefixWord ++ tailWord_6068479).sum := by decide
  have hdescent : baseEnd_6068479 < baseStart_6068479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068489 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 3]
def baseStart_6068489 : Nat := 118140960795 + 6068489 * 2 ^ 59
def prefixEnd_6068489 : Nat := 4983230072969 + 3 ^ 40 * 6068489 * 2
def baseEnd_6068489 : Nat := 3116051703522412742579033

theorem tailTrace_6068489 : CollatzResearch.WordTrace tailWord_6068489 prefixEnd_6068489 3116051703522412742579033 := by
  unfold tailWord_6068489
  simp only [CollatzResearch.WordTrace]
  refine ⟨221335977311908243253064521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147557318207938828835376347 221335977311908243253064521)
  ·
    refine ⟨166001982983931182439798391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221335977311908243253064521 166001982983931182439798391)
    ·
      refine ⟨249002974475896773659697587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166001982983931182439798391 249002974475896773659697587)
      ·
        refine ⟨373504461713845160489546381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249002974475896773659697587 373504461713845160489546381)
        ·
          refine ⟨140064173142691935183579893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373504461713845160489546381 140064173142691935183579893)
          ·
            refine ⟨13131016232127368923460615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140064173142691935183579893 13131016232127368923460615)
            ·
              refine ⟨19696524348191053385190923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13131016232127368923460615 19696524348191053385190923)
              ·
                refine ⟨29544786522286580077786385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19696524348191053385190923 29544786522286580077786385)
                ·
                  refine ⟨22158589891714935058339789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29544786522286580077786385 22158589891714935058339789)
                  ·
                    refine ⟨8309471209393100646877421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22158589891714935058339789 8309471209393100646877421)
                    ·
                      refine ⟨3116051703522412742579033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8309471209393100646877421 3116051703522412742579033)
                      ·
                        rfl

theorem cell23_6068489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_6068489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068489 prefixEnd_6068489 := by exact prefixLift 6068489
  have htrace : WordTrace (prefixWord ++ tailWord_6068489) baseStart_6068489 baseEnd_6068489 := by
    simpa [prefixWord, tailWord_6068489, baseEnd_6068489] using wordTrace_append hprefix tailTrace_6068489
  have hstable : (prefixWord ++ tailWord_6068489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068489).length < 2 ^ (prefixWord ++ tailWord_6068489).sum := by decide
  have hdescent : baseEnd_6068489 < baseStart_6068489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068492 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_6068492 : Nat := 118140960795 + 6068492 * 2 ^ 59
def prefixEnd_6068492 : Nat := 4983230072969 + 3 ^ 40 * 6068492 * 2
def baseEnd_6068492 : Nat := 1038684414654792076947173

theorem tailTrace_6068492 : CollatzResearch.WordTrace tailWord_6068492 prefixEnd_6068492 1038684414654792076947173 := by
  unfold tailWord_6068492
  simp only [CollatzResearch.WordTrace]
  refine ⟨110668043365448687382711865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147557391153931583176949153 110668043365448687382711865)
  ·
    refine ⟨83001032524086515537033899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110668043365448687382711865 83001032524086515537033899)
    ·
      refine ⟨124501548786129773305550849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83001032524086515537033899 124501548786129773305550849)
      ·
        refine ⟨93376161589597329979163137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124501548786129773305550849 93376161589597329979163137)
        ·
          refine ⟨70032121192197997484372353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93376161589597329979163137 70032121192197997484372353)
          ·
            refine ⟨52524090894148498113279265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70032121192197997484372353 52524090894148498113279265)
            ·
              refine ⟨39393068170611373584959449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52524090894148498113279265 39393068170611373584959449)
              ·
                refine ⟨29544801127958530188719587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39393068170611373584959449 29544801127958530188719587)
                ·
                  refine ⟨44317201691937795283079381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29544801127958530188719587 44317201691937795283079381)
                  ·
                    refine ⟨1038684414654792076947173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44317201691937795283079381 1038684414654792076947173)
                    ·
                      rfl

theorem cell23_6068492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_6068492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068492 prefixEnd_6068492 := by exact prefixLift 6068492
  have htrace : WordTrace (prefixWord ++ tailWord_6068492) baseStart_6068492 baseEnd_6068492 := by
    simpa [prefixWord, tailWord_6068492, baseEnd_6068492] using wordTrace_append hprefix tailTrace_6068492
  have hstable : (prefixWord ++ tailWord_6068492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068492).length < 2 ^ (prefixWord ++ tailWord_6068492).sum := by decide
  have hdescent : baseEnd_6068492 < baseStart_6068492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068647 : List Nat := [1, 1, 6, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_6068647 : Nat := 118140960795 + 6068647 * 2 ^ 59
def prefixEnd_6068647 : Nat := 4983230072969 + 3 ^ 40 * 6068647 * 2
def baseEnd_6068647 : Nat := 3116132833465823124403307

theorem tailTrace_6068647 : CollatzResearch.WordTrace tailWord_6068647 prefixEnd_6068647 3116132833465823124403307 := by
  unfold tailWord_6068647
  simp only [CollatzResearch.WordTrace]
  refine ⟨221341740045335836237316195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147561160030223890824877463 221341740045335836237316195)
  ·
    refine ⟨332012610068003754355974293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221341740045335836237316195 332012610068003754355974293)
    ·
      refine ⟨15563091096937675985436295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 332012610068003754355974293 15563091096937675985436295)
      ·
        refine ⟨23344636645406513978154443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15563091096937675985436295 23344636645406513978154443)
        ·
          refine ⟨35016954968109770967231665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23344636645406513978154443 35016954968109770967231665)
          ·
            refine ⟨26262716226082328225423749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35016954968109770967231665 26262716226082328225423749)
            ·
              refine ⟨4924259292390436542266953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26262716226082328225423749 4924259292390436542266953)
              ·
                refine ⟨3693194469292827406700215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924259292390436542266953 3693194469292827406700215)
                ·
                  refine ⟨5539791703939241110050323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693194469292827406700215 5539791703939241110050323)
                  ·
                    refine ⟨8309687555908861665075485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5539791703939241110050323 8309687555908861665075485)
                    ·
                      refine ⟨3116132833465823124403307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8309687555908861665075485 3116132833465823124403307)
                      ·
                        rfl

theorem cell23_6068647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_6068647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068647 prefixEnd_6068647 := by exact prefixLift 6068647
  have htrace : WordTrace (prefixWord ++ tailWord_6068647) baseStart_6068647 baseEnd_6068647 := by
    simpa [prefixWord, tailWord_6068647, baseEnd_6068647] using wordTrace_append hprefix tailTrace_6068647
  have hstable : (prefixWord ++ tailWord_6068647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068647).length < 2 ^ (prefixWord ++ tailWord_6068647).sum := by decide
  have hdescent : baseEnd_6068647 < baseStart_6068647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068703 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 3]
def baseStart_6068703 : Nat := 118140960795 + 6068703 * 2 ^ 59
def prefixEnd_6068703 : Nat := 4983230072969 + 3 ^ 40 * 6068703 * 2
def baseEnd_6068703 : Nat := 3116161588382474905303049

theorem tailTrace_6068703 : CollatzResearch.WordTrace tailWord_6068703 prefixEnd_6068703 3116161588382474905303049 := by
  unfold tailWord_6068703
  simp only [CollatzResearch.WordTrace]
  refine ⟨221343782533132957801354763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147562521688755305200903175 221343782533132957801354763)
  ·
    refine ⟨332015673799699436702032145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221343782533132957801354763 332015673799699436702032145)
    ·
      refine ⟨249011755349774577526524109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332015673799699436702032145 249011755349774577526524109)
      ·
        refine ⟨93379408256165466572446541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249011755349774577526524109 93379408256165466572446541)
        ·
          refine ⟨35017278096062049964667453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93379408256165466572446541 35017278096062049964667453)
          ·
            refine ⟨13131479286023268736750295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35017278096062049964667453 13131479286023268736750295)
            ·
              refine ⟨19697218929034903105125443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13131479286023268736750295 19697218929034903105125443)
              ·
                refine ⟨29545828393552354657688165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19697218929034903105125443 29545828393552354657688165)
                ·
                  refine ⟨5539842823791066498316531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29545828393552354657688165 5539842823791066498316531)
                  ·
                    refine ⟨8309764235686599747474797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5539842823791066498316531 8309764235686599747474797)
                    ·
                      refine ⟨3116161588382474905303049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8309764235686599747474797 3116161588382474905303049)
                      ·
                        rfl

theorem cell23_6068703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_6068703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068703 prefixEnd_6068703 := by exact prefixLift 6068703
  have htrace : WordTrace (prefixWord ++ tailWord_6068703) baseStart_6068703 baseEnd_6068703 := by
    simpa [prefixWord, tailWord_6068703, baseEnd_6068703] using wordTrace_append hprefix tailTrace_6068703
  have hstable : (prefixWord ++ tailWord_6068703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068703).length < 2 ^ (prefixWord ++ tailWord_6068703).sum := by decide
  have hdescent : baseEnd_6068703 < baseStart_6068703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068720 : List Nat := [2, 1, 1, 1, 3, 3, 5, 1, 2, 1, 3]
def baseStart_6068720 : Nat := 118140960795 + 6068720 * 2 ^ 59
def prefixEnd_6068720 : Nat := 4983230072969 + 3 ^ 40 * 6068720 * 2
def baseEnd_6068720 : Nat := 3116170317553601338790471

theorem tailTrace_6068720 : CollatzResearch.WordTrace tailWord_6068720 prefixEnd_6068720 3116170317553601338790471 := by
  unfold tailWord_6068720
  simp only [CollatzResearch.WordTrace]
  refine ⟨110672201287035684852361807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147562935049380913136482409 110672201287035684852361807)
  ·
    refine ⟨166008301930553527278542711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110672201287035684852361807 166008301930553527278542711)
    ·
      refine ⟨249012452895830290917814067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166008301930553527278542711 249012452895830290917814067)
      ·
        refine ⟨373518679343745436376721101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249012452895830290917814067 373518679343745436376721101)
        ·
          refine ⟨140069504753904538641270413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373518679343745436376721101 140069504753904538641270413)
          ·
            refine ⟨52526064282714201990476405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140069504753904538641270413 52526064282714201990476405)
            ·
              refine ⟨4924318526504456436607163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52526064282714201990476405 4924318526504456436607163)
              ·
                refine ⟨7386477789756684654910745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924318526504456436607163 7386477789756684654910745)
                ·
                  refine ⟨5539858342317513491183059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7386477789756684654910745 5539858342317513491183059)
                  ·
                    refine ⟨8309787513476270236774589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5539858342317513491183059 8309787513476270236774589)
                    ·
                      refine ⟨3116170317553601338790471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8309787513476270236774589 3116170317553601338790471)
                      ·
                        rfl

theorem cell23_6068720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 1, 2, 1, 3].length) (baseStart_6068720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068720 prefixEnd_6068720 := by exact prefixLift 6068720
  have htrace : WordTrace (prefixWord ++ tailWord_6068720) baseStart_6068720 baseEnd_6068720 := by
    simpa [prefixWord, tailWord_6068720, baseEnd_6068720] using wordTrace_append hprefix tailTrace_6068720
  have hstable : (prefixWord ++ tailWord_6068720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068720).length < 2 ^ (prefixWord ++ tailWord_6068720).sum := by decide
  have hdescent : baseEnd_6068720 < baseStart_6068720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068738 : List Nat := [3, 4, 1, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6068738 : Nat := 118140960795 + 6068738 * 2 ^ 59
def prefixEnd_6068738 : Nat := 4983230072969 + 3 ^ 40 * 6068738 * 2
def baseEnd_6068738 : Nat := 3116179560205382268365389

theorem tailTrace_6068738 : CollatzResearch.WordTrace tailWord_6068738 prefixEnd_6068738 3116179560205382268365389 := by
  unfold tailWord_6068738
  simp only [CollatzResearch.WordTrace]
  refine ⟨55336264772001539694719717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147563372725337439185919245 55336264772001539694719717)
  ·
    refine ⟨10375549644750288692759947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55336264772001539694719717 10375549644750288692759947)
    ·
      refine ⟨15563324467125433039139921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10375549644750288692759947 15563324467125433039139921)
      ·
        refine ⟨11672493350344074779354941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15563324467125433039139921 11672493350344074779354941)
        ·
          refine ⟨4377185006379028042258103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11672493350344074779354941 4377185006379028042258103)
          ·
            refine ⟨6565777509568542063387155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377185006379028042258103 6565777509568542063387155)
            ·
              refine ⟨9848666264352813095080733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6565777509568542063387155 9848666264352813095080733)
              ·
                refine ⟨3693249849132304910655275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9848666264352813095080733 3693249849132304910655275)
                ·
                  refine ⟨5539874773698457365982913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693249849132304910655275 5539874773698457365982913)
                  ·
                    refine ⟨4154906080273843024487185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539874773698457365982913 4154906080273843024487185)
                    ·
                      refine ⟨3116179560205382268365389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154906080273843024487185 3116179560205382268365389)
                      ·
                        rfl

theorem cell23_6068738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6068738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068738 prefixEnd_6068738 := by exact prefixLift 6068738
  have htrace : WordTrace (prefixWord ++ tailWord_6068738) baseStart_6068738 baseEnd_6068738 := by
    simpa [prefixWord, tailWord_6068738, baseEnd_6068738] using wordTrace_append hprefix tailTrace_6068738
  have hstable : (prefixWord ++ tailWord_6068738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068738).length < 2 ^ (prefixWord ++ tailWord_6068738).sum := by decide
  have hdescent : baseEnd_6068738 < baseStart_6068738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068746 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6068746 : Nat := 118140960795 + 6068746 * 2 ^ 59
def prefixEnd_6068746 : Nat := 4983230072969 + 3 ^ 40 * 6068746 * 2
def baseEnd_6068746 : Nat := 3116183668050618237065351

theorem tailTrace_6068746 : CollatzResearch.WordTrace tailWord_6068746 prefixEnd_6068746 3116183668050618237065351 := by
  unfold tailWord_6068746
  simp only [CollatzResearch.WordTrace]
  refine ⟨55336337717994294036292523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147563567247984784096780061 55336337717994294036292523)
  ·
    refine ⟨83004506576991441054438785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55336337717994294036292523 83004506576991441054438785)
    ·
      refine ⟨62253379932743580790829089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83004506576991441054438785 62253379932743580790829089)
      ·
        refine ⟨46690034949557685593121817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62253379932743580790829089 46690034949557685593121817)
        ·
          refine ⟨35017526212168264194841363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46690034949557685593121817 35017526212168264194841363)
          ·
            refine ⟨52526289318252396292262045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35017526212168264194841363 52526289318252396292262045)
            ·
              refine ⟨19697358494344648609598267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52526289318252396292262045 19697358494344648609598267)
              ·
                refine ⟨29546037741516972914397401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19697358494344648609598267 29546037741516972914397401)
                ·
                  refine ⟨22159528306137729685798051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29546037741516972914397401 22159528306137729685798051)
                  ·
                    refine ⟨33239292459206594528697077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22159528306137729685798051 33239292459206594528697077)
                    ·
                      refine ⟨3116183668050618237065351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33239292459206594528697077 3116183668050618237065351)
                      ·
                        rfl

theorem cell23_6068746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6068746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068746 prefixEnd_6068746 := by exact prefixLift 6068746
  have htrace : WordTrace (prefixWord ++ tailWord_6068746) baseStart_6068746 baseEnd_6068746 := by
    simpa [prefixWord, tailWord_6068746, baseEnd_6068746] using wordTrace_append hprefix tailTrace_6068746
  have hstable : (prefixWord ++ tailWord_6068746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068746).length < 2 ^ (prefixWord ++ tailWord_6068746).sum := by decide
  have hdescent : baseEnd_6068746 < baseStart_6068746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068760 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 4, 2, 2]
def baseStart_6068760 : Nat := 118140960795 + 6068760 * 2 ^ 59
def prefixEnd_6068760 : Nat := 4983230072969 + 3 ^ 40 * 6068760 * 2
def baseEnd_6068760 : Nat := 3116190856779781182290287

theorem tailTrace_6068760 : CollatzResearch.WordTrace tailWord_6068760 prefixEnd_6068760 3116190856779781182290287 := by
  unfold tailWord_6068760
  simp only [CollatzResearch.WordTrace]
  refine ⟨110672930746963228268089867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147563907662617637690786489 110672930746963228268089867)
  ·
    refine ⟨166009396120444842402134801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110672930746963228268089867 166009396120444842402134801)
    ·
      refine ⟨124507047090333631801601101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166009396120444842402134801 124507047090333631801601101)
      ·
        refine ⟨46690142658875111925600413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124507047090333631801601101 46690142658875111925600413)
        ·
          refine ⟨17508803497078166972100155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46690142658875111925600413 17508803497078166972100155)
          ·
            refine ⟨26263205245617250458150233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17508803497078166972100155 26263205245617250458150233)
            ·
              refine ⟨19697403934212937843612675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26263205245617250458150233 19697403934212937843612675)
              ·
                refine ⟨29546105901319406765419013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19697403934212937843612675 29546105901319406765419013)
                ·
                  refine ⟨5539894856497388768516065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29546105901319406765419013 5539894856497388768516065)
                  ·
                    refine ⟨4154921142373041576387049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5539894856497388768516065 4154921142373041576387049)
                    ·
                      refine ⟨3116190856779781182290287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154921142373041576387049 3116190856779781182290287)
                      ·
                        rfl

theorem cell23_6068760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_6068760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068760 prefixEnd_6068760 := by exact prefixLift 6068760
  have htrace : WordTrace (prefixWord ++ tailWord_6068760) baseStart_6068760 baseEnd_6068760 := by
    simpa [prefixWord, tailWord_6068760, baseEnd_6068760] using wordTrace_append hprefix tailTrace_6068760
  have hstable : (prefixWord ++ tailWord_6068760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068760).length < 2 ^ (prefixWord ++ tailWord_6068760).sum := by decide
  have hdescent : baseEnd_6068760 < baseStart_6068760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068779 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 3, 7]
def baseStart_6068779 : Nat := 118140960795 + 6068779 * 2 ^ 59
def prefixEnd_6068779 : Nat := 4983230072969 + 3 ^ 40 * 6068779 * 2
def baseEnd_6068779 : Nat := 1038733537637405535984233

theorem tailTrace_6068779 : CollatzResearch.WordTrace tailWord_6068779 prefixEnd_6068779 1038733537637405535984233 := by
  unfold tailWord_6068779
  simp only [CollatzResearch.WordTrace]
  refine ⟨221346554480857622781121391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147564369653905081854080927 221346554480857622781121391)
  ·
    refine ⟨332019831721286434171682087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221346554480857622781121391 332019831721286434171682087)
    ·
      refine ⟨498029747581929651257523131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332019831721286434171682087 498029747581929651257523131)
      ·
        refine ⟨747044621372894476886284697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498029747581929651257523131 747044621372894476886284697)
        ·
          refine ⟨560283466029670857664713523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747044621372894476886284697 560283466029670857664713523)
          ·
            refine ⟨840425199044506286497070285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560283466029670857664713523 840425199044506286497070285)
            ·
              refine ⟨315159449641689857436401357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 840425199044506286497070285 315159449641689857436401357)
              ·
                refine ⟨118184793615633696538650509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315159449641689857436401357 118184793615633696538650509)
                ·
                  refine ⟨44319297605862636201993941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118184793615633696538650509 44319297605862636201993941)
                  ·
                    refine ⟨1038733537637405535984233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44319297605862636201993941 1038733537637405535984233)
                    ·
                      rfl

theorem cell23_6068779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_6068779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068779 prefixEnd_6068779 := by exact prefixLift 6068779
  have htrace : WordTrace (prefixWord ++ tailWord_6068779) baseStart_6068779 baseEnd_6068779 := by
    simpa [prefixWord, tailWord_6068779, baseEnd_6068779] using wordTrace_append hprefix tailTrace_6068779
  have hstable : (prefixWord ++ tailWord_6068779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068779).length < 2 ^ (prefixWord ++ tailWord_6068779).sum := by decide
  have hdescent : baseEnd_6068779 < baseStart_6068779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068816 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_6068816 : Nat := 118140960795 + 6068816 * 2 ^ 59
def prefixEnd_6068816 : Nat := 4983230072969 + 3 ^ 40 * 6068816 * 2
def baseEnd_6068816 : Nat := 3116219611696432963190029

theorem tailTrace_6068816 : CollatzResearch.WordTrace tailWord_6068816 prefixEnd_6068816 3116219611696432963190029 := by
  unfold tailWord_6068816
  simp only [CollatzResearch.WordTrace]
  refine ⟨110673951990861789050109151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147565269321149052066812201 110673951990861789050109151)
  ·
    refine ⟨166010927986292683575163727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110673951990861789050109151 166010927986292683575163727)
    ·
      refine ⟨249016391979439025362745591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166010927986292683575163727 249016391979439025362745591)
      ·
        refine ⟨373524587969158538044118387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249016391979439025362745591 373524587969158538044118387)
        ·
          refine ⟨560286881953737807066177581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373524587969158538044118387 560286881953737807066177581)
          ·
            refine ⟨210107580732651677649816593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560286881953737807066177581 210107580732651677649816593)
            ·
              refine ⟨157580685549488758237362445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210107580732651677649816593 157580685549488758237362445)
              ·
                refine ⟨59092757081058284339010917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157580685549488758237362445 59092757081058284339010917)
                ·
                  refine ⟨11079891952698428313564547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59092757081058284339010917 11079891952698428313564547)
                  ·
                    refine ⟨16619837929047642470346821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11079891952698428313564547 16619837929047642470346821)
                    ·
                      refine ⟨3116219611696432963190029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16619837929047642470346821 3116219611696432963190029)
                      ·
                        rfl

theorem cell23_6068816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_6068816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068816 prefixEnd_6068816 := by exact prefixLift 6068816
  have htrace : WordTrace (prefixWord ++ tailWord_6068816) baseStart_6068816 baseEnd_6068816 := by
    simpa [prefixWord, tailWord_6068816, baseEnd_6068816] using wordTrace_append hprefix tailTrace_6068816
  have hstable : (prefixWord ++ tailWord_6068816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068816).length < 2 ^ (prefixWord ++ tailWord_6068816).sum := by decide
  have hdescent : baseEnd_6068816 < baseStart_6068816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068833 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_6068833 : Nat := 118140960795 + 6068833 * 2 ^ 59
def prefixEnd_6068833 : Nat := 4983230072969 + 3 ^ 40 * 6068833 * 2
def baseEnd_6068833 : Nat := 3116228340867559396677451

theorem tailTrace_6068833 : CollatzResearch.WordTrace tailWord_6068833 prefixEnd_6068833 3116228340867559396677451 := by
  unfold tailWord_6068833
  simp only [CollatzResearch.WordTrace]
  refine ⟨221348524022661990003587153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147565682681774660002391435 221348524022661990003587153)
  ·
    refine ⟨166011393016996492502690365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221348524022661990003587153 166011393016996492502690365)
    ·
      refine ⟨62254272381373684688508887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166011393016996492502690365 62254272381373684688508887)
      ·
        refine ⟨93381408572060527032763331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62254272381373684688508887 93381408572060527032763331)
        ·
          refine ⟨140072112858090790549144997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93381408572060527032763331 140072112858090790549144997)
          ·
            refine ⟨26263521160892023227964687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140072112858090790549144997 26263521160892023227964687)
            ·
              refine ⟨39395281741338034841947031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26263521160892023227964687 39395281741338034841947031)
              ·
                refine ⟨59092922612007052262920547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39395281741338034841947031 59092922612007052262920547)
                ·
                  refine ⟨88639383918010578394380821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59092922612007052262920547 88639383918010578394380821)
                  ·
                    refine ⟨4154971121156745862236601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88639383918010578394380821 4154971121156745862236601)
                    ·
                      refine ⟨3116228340867559396677451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4154971121156745862236601 3116228340867559396677451)
                      ·
                        rfl

theorem cell23_6068833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_6068833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068833 prefixEnd_6068833 := by exact prefixLift 6068833
  have htrace : WordTrace (prefixWord ++ tailWord_6068833) baseStart_6068833 baseEnd_6068833 := by
    simpa [prefixWord, tailWord_6068833, baseEnd_6068833] using wordTrace_append hprefix tailTrace_6068833
  have hstable : (prefixWord ++ tailWord_6068833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068833).length < 2 ^ (prefixWord ++ tailWord_6068833).sum := by decide
  have hdescent : baseEnd_6068833 < baseStart_6068833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068860 : List Nat := [2, 2, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_6068860 : Nat := 118140960795 + 6068860 * 2 ^ 59
def prefixEnd_6068860 : Nat := 4983230072969 + 3 ^ 40 * 6068860 * 2
def baseEnd_6068860 : Nat := 1038747401615076930346609

theorem tailTrace_6068860 : CollatzResearch.WordTrace tailWord_6068860 prefixEnd_6068860 1038747401615076930346609 := by
  unfold tailWord_6068860
  simp only [CollatzResearch.WordTrace]
  refine ⟨110674754396782086807410017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147566339195709449076546689 110674754396782086807410017)
  ·
    refine ⟨83006065797586565105557513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110674754396782086807410017 83006065797586565105557513)
    ·
      refine ⟨62254549348189923829168135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83006065797586565105557513 62254549348189923829168135)
      ·
        refine ⟨93381824022284885743752203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62254549348189923829168135 93381824022284885743752203)
        ·
          refine ⟨140072736033427328615628305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93381824022284885743752203 140072736033427328615628305)
          ·
            refine ⟨105054552025070496461721229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140072736033427328615628305 105054552025070496461721229)
            ·
              refine ⟨39395457009401436173145461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105054552025070496461721229 39395457009401436173145461)
              ·
                refine ⟨3693324094631384641232387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39395457009401436173145461 3693324094631384641232387)
                ·
                  refine ⟨5539986141947076961848581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693324094631384641232387 5539986141947076961848581)
                  ·
                    refine ⟨1038747401615076930346609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5539986141947076961848581 1038747401615076930346609)
                    ·
                      rfl

theorem cell23_6068860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_6068860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068860 prefixEnd_6068860 := by exact prefixLift 6068860
  have htrace : WordTrace (prefixWord ++ tailWord_6068860) baseStart_6068860 baseEnd_6068860 := by
    simpa [prefixWord, tailWord_6068860, baseEnd_6068860] using wordTrace_append hprefix tailTrace_6068860
  have hstable : (prefixWord ++ tailWord_6068860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068860).length < 2 ^ (prefixWord ++ tailWord_6068860).sum := by decide
  have hdescent : baseEnd_6068860 < baseStart_6068860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068883 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 3]
def baseStart_6068883 : Nat := 118140960795 + 6068883 * 2 ^ 59
def prefixEnd_6068883 : Nat := 4983230072969 + 3 ^ 40 * 6068883 * 2
def baseEnd_6068883 : Nat := 3116254014900284201052221

theorem tailTrace_6068883 : CollatzResearch.WordTrace tailWord_6068883 prefixEnd_6068883 3116254014900284201052221 := by
  unfold tailWord_6068883
  simp only [CollatzResearch.WordTrace]
  refine ⟨221350347672480848542907303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147566898448320565695271535 221350347672480848542907303)
  ·
    refine ⟨332025521508721272814360955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221350347672480848542907303 332025521508721272814360955)
    ·
      refine ⟨498038282263081909221541433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332025521508721272814360955 498038282263081909221541433)
      ·
        refine ⟨373528711697311431916156075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498038282263081909221541433 373528711697311431916156075)
        ·
          refine ⟨560293067545967147874234113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373528711697311431916156075 560293067545967147874234113)
          ·
            refine ⟨420219800659475360905675585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560293067545967147874234113 420219800659475360905675585)
            ·
              refine ⟨315164850494606520679256689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420219800659475360905675585 315164850494606520679256689)
              ·
                refine ⟨236373637870954890509442517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315164850494606520679256689 236373637870954890509442517)
                ·
                  refine ⟨5540007137600505246315059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 236373637870954890509442517 5540007137600505246315059)
                  ·
                    refine ⟨8310010706400757869472589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5540007137600505246315059 8310010706400757869472589)
                    ·
                      refine ⟨3116254014900284201052221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8310010706400757869472589 3116254014900284201052221)
                      ·
                        rfl

theorem cell23_6068883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 3].length) (baseStart_6068883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068883 prefixEnd_6068883 := by exact prefixLift 6068883
  have htrace : WordTrace (prefixWord ++ tailWord_6068883) baseStart_6068883 baseEnd_6068883 := by
    simpa [prefixWord, tailWord_6068883, baseEnd_6068883] using wordTrace_append hprefix tailTrace_6068883
  have hstable : (prefixWord ++ tailWord_6068883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068883).length < 2 ^ (prefixWord ++ tailWord_6068883).sum := by decide
  have hdescent : baseEnd_6068883 < baseStart_6068883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068900 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_6068900 : Nat := 118140960795 + 6068900 * 2 ^ 59
def prefixEnd_6068900 : Nat := 4983230072969 + 3 ^ 40 * 6068900 * 2
def baseEnd_6068900 : Nat := 3116262744071410634539643

theorem tailTrace_6068900 : CollatzResearch.WordTrace tailWord_6068900 prefixEnd_6068900 3116262744071410634539643 := by
  unfold tailWord_6068900
  simp only [CollatzResearch.WordTrace]
  refine ⟨110675483856709630223138077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147567311808946173630850769 110675483856709630223138077)
  ·
    refine ⟨41503306446266111333676779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110675483856709630223138077 41503306446266111333676779)
    ·
      refine ⟨62254959669399167000515169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41503306446266111333676779 62254959669399167000515169)
      ·
        refine ⟨46691219752049375250386377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62254959669399167000515169 46691219752049375250386377)
        ·
          refine ⟨35018414814037031437789783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46691219752049375250386377 35018414814037031437789783)
          ·
            refine ⟨52527622221055547156684675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35018414814037031437789783 52527622221055547156684675)
            ·
              refine ⟨78791433331583320735027013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52527622221055547156684675 78791433331583320735027013)
              ·
                refine ⟨14773393749671872637817565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78791433331583320735027013 14773393749671872637817565)
                ·
                  refine ⟨5540022656126952239181587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14773393749671872637817565 5540022656126952239181587)
                  ·
                    refine ⟨8310033984190428358772381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5540022656126952239181587 8310033984190428358772381)
                    ·
                      refine ⟨3116262744071410634539643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8310033984190428358772381 3116262744071410634539643)
                      ·
                        rfl

theorem cell23_6068900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_6068900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068900 prefixEnd_6068900 := by exact prefixLift 6068900
  have htrace : WordTrace (prefixWord ++ tailWord_6068900) baseStart_6068900 baseEnd_6068900 := by
    simpa [prefixWord, tailWord_6068900, baseEnd_6068900] using wordTrace_append hprefix tailTrace_6068900
  have hstable : (prefixWord ++ tailWord_6068900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068900).length < 2 ^ (prefixWord ++ tailWord_6068900).sum := by decide
  have hdescent : baseEnd_6068900 < baseStart_6068900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068941 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 6]
def baseStart_6068941 : Nat := 118140960795 + 6068941 * 2 ^ 59
def prefixEnd_6068941 : Nat := 4983230072969 + 3 ^ 40 * 6068941 * 2
def baseEnd_6068941 : Nat := 346253755197582774902995

theorem tailTrace_6068941 : CollatzResearch.WordTrace tailWord_6068941 prefixEnd_6068941 346253755197582774902995 := by
  unfold tailWord_6068941
  simp only [CollatzResearch.WordTrace]
  refine ⟨221352463106270724448518677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147568308737513816299012451 221352463106270724448518677)
  ·
    refine ⟨10375896708106440208524313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221352463106270724448518677 10375896708106440208524313)
    ·
      refine ⟨7781922531079830156393235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10375896708106440208524313 7781922531079830156393235)
      ·
        refine ⟨11672883796619745234589853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781922531079830156393235 11672883796619745234589853)
        ·
          refine ⟨4377331423732404462971195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11672883796619745234589853 4377331423732404462971195)
          ·
            refine ⟨6565997135598606694456793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377331423732404462971195 6565997135598606694456793)
            ·
              refine ⟨4924497851698955020842595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565997135598606694456793 4924497851698955020842595)
              ·
                refine ⟨7386746777548432531263893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924497851698955020842595 7386746777548432531263893)
                ·
                  refine ⟨346253755197582774902995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7386746777548432531263893 346253755197582774902995)
                  ·
                    rfl

theorem cell23_6068941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_6068941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068941 prefixEnd_6068941 := by exact prefixLift 6068941
  have htrace : WordTrace (prefixWord ++ tailWord_6068941) baseStart_6068941 baseEnd_6068941 := by
    simpa [prefixWord, tailWord_6068941, baseEnd_6068941] using wordTrace_append hprefix tailTrace_6068941
  have hstable : (prefixWord ++ tailWord_6068941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068941).length < 2 ^ (prefixWord ++ tailWord_6068941).sum := by decide
  have hdescent : baseEnd_6068941 < baseStart_6068941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068953 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_6068953 : Nat := 118140960795 + 6068953 * 2 ^ 59
def prefixEnd_6068953 : Nat := 4983230072969 + 3 ^ 40 * 6068953 * 2
def baseEnd_6068953 : Nat := 3116289958546098927176899

theorem tailTrace_6068953 : CollatzResearch.WordTrace tailWord_6068953 prefixEnd_6068953 3116289958546098927176899 := by
  unfold tailWord_6068953
  simp only [CollatzResearch.WordTrace]
  refine ⟨221352900782227250497955513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147568600521484833665303675 221352900782227250497955513)
  ·
    refine ⟨166014675586670437873466635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221352900782227250497955513 166014675586670437873466635)
    ·
      refine ⟨249022013380005656810199953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166014675586670437873466635 249022013380005656810199953)
      ·
        refine ⟨186766510035004242607649965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249022013380005656810199953 186766510035004242607649965)
        ·
          refine ⟨70037441263126590977868737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186766510035004242607649965 70037441263126590977868737)
          ·
            refine ⟨52528080947344943233401553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70037441263126590977868737 52528080947344943233401553)
            ·
              refine ⟨39396060710508707425051165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52528080947344943233401553 39396060710508707425051165)
              ·
                refine ⟨14773522766440765284394187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39396060710508707425051165 14773522766440765284394187)
                ·
                  refine ⟨22160284149661147926591281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14773522766440765284394187 22160284149661147926591281)
                  ·
                    refine ⟨16620213112245860944943461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22160284149661147926591281 16620213112245860944943461)
                    ·
                      refine ⟨3116289958546098927176899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16620213112245860944943461 3116289958546098927176899)
                      ·
                        rfl

theorem cell23_6068953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_6068953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068953 prefixEnd_6068953 := by exact prefixLift 6068953
  have htrace : WordTrace (prefixWord ++ tailWord_6068953) baseStart_6068953 baseEnd_6068953 := by
    simpa [prefixWord, tailWord_6068953, baseEnd_6068953] using wordTrace_append hprefix tailTrace_6068953
  have hstable : (prefixWord ++ tailWord_6068953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068953).length < 2 ^ (prefixWord ++ tailWord_6068953).sum := by decide
  have hdescent : baseEnd_6068953 < baseStart_6068953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068963 : List Nat := [1, 1, 1, 7, 1, 1, 2, 9]
def baseStart_6068963 : Nat := 118140960795 + 6068963 * 2 ^ 59
def prefixEnd_6068963 : Nat := 4983230072969 + 3 ^ 40 * 6068963 * 2
def baseEnd_6068963 : Nat := 115418336790838662520439

theorem tailTrace_6068963 : CollatzResearch.WordTrace tailWord_6068963 prefixEnd_6068963 115418336790838662520439 := by
  unfold tailWord_6068963
  simp only [CollatzResearch.WordTrace]
  refine ⟨221353265512191022205819543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147568843674794014803879695 221353265512191022205819543)
  ·
    refine ⟨332029898268286533308729315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221353265512191022205819543 332029898268286533308729315)
    ·
      refine ⟨498044847402429799963093973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332029898268286533308729315 498044847402429799963093973)
      ·
        refine ⟨11672926110994448436635015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 498044847402429799963093973 11672926110994448436635015)
        ·
          refine ⟨17509389166491672654952523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11672926110994448436635015 17509389166491672654952523)
          ·
            refine ⟨26264083749737508982428785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17509389166491672654952523 26264083749737508982428785)
            ·
              refine ⟨19698062812303131736821589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26264083749737508982428785 19698062812303131736821589)
              ·
                refine ⟨115418336790838662520439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19698062812303131736821589 115418336790838662520439)
                ·
                  rfl

theorem cell23_6068963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 9].length) (baseStart_6068963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068963 prefixEnd_6068963 := by exact prefixLift 6068963
  have htrace : WordTrace (prefixWord ++ tailWord_6068963) baseStart_6068963 baseEnd_6068963 := by
    simpa [prefixWord, tailWord_6068963, baseEnd_6068963] using wordTrace_append hprefix tailTrace_6068963
  have hstable : (prefixWord ++ tailWord_6068963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068963).length < 2 ^ (prefixWord ++ tailWord_6068963).sum := by decide
  have hdescent : baseEnd_6068963 < baseStart_6068963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068977 : List Nat := [1, 2, 2, 2, 2, 2, 5, 1, 1, 2, 3]
def baseStart_6068977 : Nat := 118140960795 + 6068977 * 2 ^ 59
def prefixEnd_6068977 : Nat := 4983230072969 + 3 ^ 40 * 6068977 * 2
def baseEnd_6068977 : Nat := 3116302282081806833276789

theorem tailTrace_6068977 : CollatzResearch.WordTrace tailWord_6068977 prefixEnd_6068977 3116302282081806833276789 := by
  unfold tailWord_6068977
  simp only [CollatzResearch.WordTrace]
  refine ⟨221353776134140302596829185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147569184089426868397886123 221353776134140302596829185)
  ·
    refine ⟨166015332100605226947621889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221353776134140302596829185 166015332100605226947621889)
    ·
      refine ⟨124511499075453920210716417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166015332100605226947621889 124511499075453920210716417)
      ·
        refine ⟨93383624306590440158037313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124511499075453920210716417 93383624306590440158037313)
        ·
          refine ⟨70037718229942830118527985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93383624306590440158037313 70037718229942830118527985)
          ·
            refine ⟨52528288672457122588895989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70037718229942830118527985 52528288672457122588895989)
            ·
              refine ⟨4924527063042855242708999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52528288672457122588895989 4924527063042855242708999)
              ·
                refine ⟨7386790594564282864063499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924527063042855242708999 7386790594564282864063499)
                ·
                  refine ⟨11080185891846424296095249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7386790594564282864063499 11080185891846424296095249)
                  ·
                    refine ⟨8310139418884818222071437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11080185891846424296095249 8310139418884818222071437)
                    ·
                      refine ⟨3116302282081806833276789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8310139418884818222071437 3116302282081806833276789)
                      ·
                        rfl

theorem cell23_6068977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_6068977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068977 prefixEnd_6068977 := by exact prefixLift 6068977
  have htrace : WordTrace (prefixWord ++ tailWord_6068977) baseStart_6068977 baseEnd_6068977 := by
    simpa [prefixWord, tailWord_6068977, baseEnd_6068977] using wordTrace_append hprefix tailTrace_6068977
  have hstable : (prefixWord ++ tailWord_6068977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068977).length < 2 ^ (prefixWord ++ tailWord_6068977).sum := by decide
  have hdescent : baseEnd_6068977 < baseStart_6068977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6068980 : List Nat := [2, 6, 1, 1, 13]
def baseStart_6068980 : Nat := 118140960795 + 6068980 * 2 ^ 59
def prefixEnd_6068980 : Nat := 4983230072969 + 3 ^ 40 * 6068980 * 2
def baseEnd_6068980 : Nat := 4274765188647147217475

theorem tailTrace_6068980 : CollatzResearch.WordTrace tailWord_6068980 prefixEnd_6068980 4274765188647147217475 := by
  unfold tailWord_6068980
  simp only [CollatzResearch.WordTrace]
  refine ⟨110676942776564717054594197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147569257035419622739458929 110676942776564717054594197)
  ·
    refine ⟨5187981692651471111934103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110676942776564717054594197 5187981692651471111934103)
    ·
      refine ⟨7781972538977206667901155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187981692651471111934103 7781972538977206667901155)
      ·
        refine ⟨11672958808465810001851733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781972538977206667901155 11672958808465810001851733)
        ·
          refine ⟨4274765188647147217475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11672958808465810001851733 4274765188647147217475)
          ·
            rfl

theorem cell23_6068980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 13].length) (baseStart_6068980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6068980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6068980 prefixEnd_6068980 := by exact prefixLift 6068980
  have htrace : WordTrace (prefixWord ++ tailWord_6068980) baseStart_6068980 baseEnd_6068980 := by
    simpa [prefixWord, tailWord_6068980, baseEnd_6068980] using wordTrace_append hprefix tailTrace_6068980
  have hstable : (prefixWord ++ tailWord_6068980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6068980).length < 2 ^ (prefixWord ++ tailWord_6068980).sum := by decide
  have hdescent : baseEnd_6068980 < baseStart_6068980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6068980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069013 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_6069013 : Nat := 118140960795 + 6069013 * 2 ^ 59
def prefixEnd_6069013 : Nat := 4983230072969 + 3 ^ 40 * 6069013 * 2
def baseEnd_6069013 : Nat := 3116320767385368692426623

theorem tailTrace_6069013 : CollatzResearch.WordTrace tailWord_6069013 prefixEnd_6069013 3116320767385368692426623 := by
  unfold tailWord_6069013
  simp only [CollatzResearch.WordTrace]
  refine ⟨221355089162009880745139693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147570059441339920496759795 221355089162009880745139693)
  ·
    refine ⟨83008158435753705279427385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221355089162009880745139693 83008158435753705279427385)
    ·
      refine ⟨62256118826815278959570539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83008158435753705279427385 62256118826815278959570539)
      ·
        refine ⟨93384178240222918439355809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62256118826815278959570539 93384178240222918439355809)
        ·
          refine ⟨70038133680167188829516857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93384178240222918439355809 70038133680167188829516857)
          ·
            refine ⟨52528600260125391622137643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70038133680167188829516857 52528600260125391622137643)
            ·
              refine ⟨78792900390188087433206465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52528600260125391622137643 78792900390188087433206465)
              ·
                refine ⟨59094675292641065574904849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78792900390188087433206465 59094675292641065574904849)
                ·
                  refine ⟨44321006469480799181178637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59094675292641065574904849 44321006469480799181178637)
                  ·
                    refine ⟨16620377426055299692941989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44321006469480799181178637 16620377426055299692941989)
                    ·
                      refine ⟨3116320767385368692426623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16620377426055299692941989 3116320767385368692426623)
                      ·
                        rfl

theorem cell23_6069013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_6069013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069013 prefixEnd_6069013 := by exact prefixLift 6069013
  have htrace : WordTrace (prefixWord ++ tailWord_6069013) baseStart_6069013 baseEnd_6069013 := by
    simpa [prefixWord, tailWord_6069013, baseEnd_6069013] using wordTrace_append hprefix tailTrace_6069013
  have hstable : (prefixWord ++ tailWord_6069013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069013).length < 2 ^ (prefixWord ++ tailWord_6069013).sum := by decide
  have hdescent : baseEnd_6069013 < baseStart_6069013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069033 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 3]
def baseStart_6069033 : Nat := 118140960795 + 6069033 * 2 ^ 59
def prefixEnd_6069033 : Nat := 4983230072969 + 3 ^ 40 * 6069033 * 2
def baseEnd_6069033 : Nat := 3116331036998458614176531

theorem tailTrace_6069033 : CollatzResearch.WordTrace tailWord_6069033 prefixEnd_6069033 3116331036998458614176531 := by
  unfold tailWord_6069033
  simp only [CollatzResearch.WordTrace]
  refine ⟨221355818621937424160867753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147570545747958282773911835 221355818621937424160867753)
  ·
    refine ⟨166016863966453068120650815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221355818621937424160867753 166016863966453068120650815)
    ·
      refine ⟨249025295949679602180976223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166016863966453068120650815 249025295949679602180976223)
      ·
        refine ⟨373537943924519403271464335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249025295949679602180976223 373537943924519403271464335)
        ·
          refine ⟨560306915886779104907196503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373537943924519403271464335 560306915886779104907196503)
          ·
            refine ⟨840460373830168657360794755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560306915886779104907196503 840460373830168657360794755)
            ·
              refine ⟨1260690560745252986041192133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840460373830168657360794755 1260690560745252986041192133)
              ·
                refine ⟨236379480139734934882723525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1260690560745252986041192133 236379480139734934882723525)
                ·
                  refine ⟨44321152526200300290510661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236379480139734934882723525 44321152526200300290510661)
                  ·
                    refine ⟨8310216098662556304470749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44321152526200300290510661 8310216098662556304470749)
                    ·
                      refine ⟨3116331036998458614176531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8310216098662556304470749 3116331036998458614176531)
                      ·
                        rfl

theorem cell23_6069033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_6069033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069033 prefixEnd_6069033 := by exact prefixLift 6069033
  have htrace : WordTrace (prefixWord ++ tailWord_6069033) baseStart_6069033 baseEnd_6069033 := by
    simpa [prefixWord, tailWord_6069033, baseEnd_6069033] using wordTrace_append hprefix tailTrace_6069033
  have hstable : (prefixWord ++ tailWord_6069033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069033).length < 2 ^ (prefixWord ++ tailWord_6069033).sum := by decide
  have hdescent : baseEnd_6069033 < baseStart_6069033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069047 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 4, 2, 2]
def baseStart_6069047 : Nat := 118140960795 + 6069047 * 2 ^ 59
def prefixEnd_6069047 : Nat := 4983230072969 + 3 ^ 40 * 6069047 * 2
def baseEnd_6069047 : Nat := 3116338225727621559401467

theorem tailTrace_6069047 : CollatzResearch.WordTrace tailWord_6069047 prefixEnd_6069047 3116338225727621559401467 := by
  unfold tailWord_6069047
  simp only [CollatzResearch.WordTrace]
  refine ⟨221356329243886704551877395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147570886162591136367918263 221356329243886704551877395)
  ·
    refine ⟨332034493865830056827816093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221356329243886704551877395 332034493865830056827816093)
    ·
      refine ⟨124512935199686271310431035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332034493865830056827816093 124512935199686271310431035)
      ·
        refine ⟨186769402799529406965646553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124512935199686271310431035 186769402799529406965646553)
        ·
          refine ⟨140077052099647055224234915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186769402799529406965646553 140077052099647055224234915)
          ·
            refine ⟨210115578149470582836352373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140077052099647055224234915 210115578149470582836352373)
            ·
              refine ⟨19698335451512867140908035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210115578149470582836352373 19698335451512867140908035)
              ·
                refine ⟨29547503177269300711362053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19698335451512867140908035 29547503177269300711362053)
                ·
                  refine ⟨5540156845737993883380385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29547503177269300711362053 5540156845737993883380385)
                  ·
                    refine ⟨4155117634303495412535289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5540156845737993883380385 4155117634303495412535289)
                    ·
                      refine ⟨3116338225727621559401467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4155117634303495412535289 3116338225727621559401467)
                      ·
                        rfl

theorem cell23_6069047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_6069047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069047 prefixEnd_6069047 := by exact prefixLift 6069047
  have htrace : WordTrace (prefixWord ++ tailWord_6069047) baseStart_6069047 baseEnd_6069047 := by
    simpa [prefixWord, tailWord_6069047, baseEnd_6069047] using wordTrace_append hprefix tailTrace_6069047
  have hstable : (prefixWord ++ tailWord_6069047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069047).length < 2 ^ (prefixWord ++ tailWord_6069047).sum := by decide
  have hdescent : baseEnd_6069047 < baseStart_6069047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069100 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_6069100 : Nat := 118140960795 + 6069100 * 2 ^ 59
def prefixEnd_6069100 : Nat := 4983230072969 + 3 ^ 40 * 6069100 * 2
def baseEnd_6069100 : Nat := 1038788480067436617346241

theorem tailTrace_6069100 : CollatzResearch.WordTrace tailWord_6069100 prefixEnd_6069100 1038788480067436617346241 := by
  unfold tailWord_6069100
  simp only [CollatzResearch.WordTrace]
  refine ⟨110679131156347347301778377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147572174875129796402371169 110679131156347347301778377)
  ·
    refine ⟨83009348367260510476333783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110679131156347347301778377 83009348367260510476333783)
    ·
      refine ⟨124514022550890765714500675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83009348367260510476333783 124514022550890765714500675)
      ·
        refine ⟨186771033826336148571751013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124514022550890765714500675 186771033826336148571751013)
        ·
          refine ⟨35019568842438027857203315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186771033826336148571751013 35019568842438027857203315)
          ·
            refine ⟨52529353263657041785804973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35019568842438027857203315 52529353263657041785804973)
            ·
              refine ⟨19698507473871390669676865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52529353263657041785804973 19698507473871390669676865)
              ·
                refine ⟨14773880605403543002257649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19698507473871390669676865 14773880605403543002257649)
                ·
                  refine ⟨11080410454052657251693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14773880605403543002257649 11080410454052657251693237)
                  ·
                    refine ⟨1038788480067436617346241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11080410454052657251693237 1038788480067436617346241)
                    ·
                      rfl

theorem cell23_6069100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_6069100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069100 prefixEnd_6069100 := by exact prefixLift 6069100
  have htrace : WordTrace (prefixWord ++ tailWord_6069100) baseStart_6069100 baseEnd_6069100 := by
    simpa [prefixWord, tailWord_6069100, baseEnd_6069100] using wordTrace_append hprefix tailTrace_6069100
  have hstable : (prefixWord ++ tailWord_6069100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069100).length < 2 ^ (prefixWord ++ tailWord_6069100).sum := by decide
  have hdescent : baseEnd_6069100 < baseStart_6069100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8]
def baseStart_6069163 : Nat := 118140960795 + 6069163 * 2 ^ 59
def prefixEnd_6069163 : Nat := 4983230072969 + 3 ^ 40 * 6069163 * 2
def baseEnd_6069163 : Nat := 3116397789483543105550933

theorem tailTrace_6069163 : CollatzResearch.WordTrace tailWord_6069163 prefixEnd_6069163 3116397789483543105550933 := by
  unfold tailWord_6069163
  simp only [CollatzResearch.WordTrace]
  refine ⟨221360560111466456363100143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147573706740977637575400095 221360560111466456363100143)
  ·
    refine ⟨332040840167199684544650215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221360560111466456363100143 332040840167199684544650215)
    ·
      refine ⟨498061260250799526816975323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332040840167199684544650215 498061260250799526816975323)
      ·
        refine ⟨747091890376199290225462985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498061260250799526816975323 747091890376199290225462985)
        ·
          refine ⟨560318917782149467669097239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747091890376199290225462985 560318917782149467669097239)
          ·
            refine ⟨840478376673224201503645859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560318917782149467669097239 840478376673224201503645859)
            ·
              refine ⟨1260717565009836302255468789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840478376673224201503645859 1260717565009836302255468789)
              ·
                refine ⟨118192271719672153336450199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1260717565009836302255468789 118192271719672153336450199)
                ·
                  refine ⟨177288407579508230004675299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118192271719672153336450199 177288407579508230004675299)
                  ·
                    refine ⟨265932611369262345007012949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177288407579508230004675299 265932611369262345007012949)
                    ·
                      refine ⟨3116397789483543105550933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 265932611369262345007012949 3116397789483543105550933)
                      ·
                        rfl

theorem cell23_6069163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_6069163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069163 prefixEnd_6069163 := by exact prefixLift 6069163
  have htrace : WordTrace (prefixWord ++ tailWord_6069163) baseStart_6069163 baseEnd_6069163 := by
    simpa [prefixWord, tailWord_6069163, baseEnd_6069163] using wordTrace_append hprefix tailTrace_6069163
  have hstable : (prefixWord ++ tailWord_6069163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069163).length < 2 ^ (prefixWord ++ tailWord_6069163).sum := by decide
  have hdescent : baseEnd_6069163 < baseStart_6069163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069170 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_6069170 : Nat := 118140960795 + 6069170 * 2 ^ 59
def prefixEnd_6069170 : Nat := 4983230072969 + 3 ^ 40 * 6069170 * 2
def baseEnd_6069170 : Nat := 3116401383848124578163401

theorem tailTrace_6069170 : CollatzResearch.WordTrace tailWord_6069170 prefixEnd_6069170 3116401383848124578163401 := by
  unfold tailWord_6069170
  simp only [CollatzResearch.WordTrace]
  refine ⟨55340203855610274139651241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147573876948294064372403309 55340203855610274139651241)
  ·
    refine ⟨41505152891707705604738431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55340203855610274139651241 41505152891707705604738431)
    ·
      refine ⟨62257729337561558407107647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41505152891707705604738431 62257729337561558407107647)
      ·
        refine ⟨93386594006342337610661471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62257729337561558407107647 93386594006342337610661471)
        ·
          refine ⟨140079891009513506415992207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93386594006342337610661471 140079891009513506415992207)
          ·
            refine ⟨210119836514270259623988311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140079891009513506415992207 210119836514270259623988311)
            ·
              refine ⟨315179754771405389435982467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210119836514270259623988311 315179754771405389435982467)
              ·
                refine ⟨472769632157108084153973701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315179754771405389435982467 472769632157108084153973701)
                ·
                  refine ⟨88644306029457765778870069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472769632157108084153973701 88644306029457765778870069)
                  ·
                    refine ⟨8310403690261665541769069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88644306029457765778870069 8310403690261665541769069)
                    ·
                      refine ⟨3116401383848124578163401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8310403690261665541769069 3116401383848124578163401)
                      ·
                        rfl

theorem cell23_6069170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_6069170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069170 prefixEnd_6069170 := by exact prefixLift 6069170
  have htrace : WordTrace (prefixWord ++ tailWord_6069170) baseStart_6069170 baseEnd_6069170 := by
    simpa [prefixWord, tailWord_6069170, baseEnd_6069170] using wordTrace_append hprefix tailTrace_6069170
  have hstable : (prefixWord ++ tailWord_6069170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069170).length < 2 ^ (prefixWord ++ tailWord_6069170).sum := by decide
  have hdescent : baseEnd_6069170 < baseStart_6069170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069187 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 3]
def baseStart_6069187 : Nat := 118140960795 + 6069187 * 2 ^ 59
def prefixEnd_6069187 : Nat := 4983230072969 + 3 ^ 40 * 6069187 * 2
def baseEnd_6069187 : Nat := 3116410113019251011650823

theorem tailTrace_6069187 : CollatzResearch.WordTrace tailWord_6069187 prefixEnd_6069187 3116410113019251011650823 := by
  unfold tailWord_6069187
  simp only [CollatzResearch.WordTrace]
  refine ⟨221361435463379508461973815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147574290308919672307982543 221361435463379508461973815)
  ·
    refine ⟨332042153195069262692960723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221361435463379508461973815 332042153195069262692960723)
    ·
      refine ⟨498063229792603894039441085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332042153195069262692960723 498063229792603894039441085)
      ·
        refine ⟨186773711172226460264790407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498063229792603894039441085 186773711172226460264790407)
        ·
          refine ⟨280160566758339690397185611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186773711172226460264790407 280160566758339690397185611)
          ·
            refine ⟨420240850137509535595778417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280160566758339690397185611 420240850137509535595778417)
            ·
              refine ⟨315180637603132151696833813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420240850137509535595778417 315180637603132151696833813)
              ·
                refine ⟨14774092387646819610789085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 315180637603132151696833813 14774092387646819610789085)
                ·
                  refine ⟨5540284645367557354045907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14774092387646819610789085 5540284645367557354045907)
                  ·
                    refine ⟨8310426968051336031068861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5540284645367557354045907 8310426968051336031068861)
                    ·
                      refine ⟨3116410113019251011650823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8310426968051336031068861 3116410113019251011650823)
                      ·
                        rfl

theorem cell23_6069187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_6069187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069187 prefixEnd_6069187 := by exact prefixLift 6069187
  have htrace : WordTrace (prefixWord ++ tailWord_6069187) baseStart_6069187 baseEnd_6069187 := by
    simpa [prefixWord, tailWord_6069187, baseEnd_6069187] using wordTrace_append hprefix tailTrace_6069187
  have hstable : (prefixWord ++ tailWord_6069187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069187).length < 2 ^ (prefixWord ++ tailWord_6069187).sum := by decide
  have hdescent : baseEnd_6069187 < baseStart_6069187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069188 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_6069188 : Nat := 118140960795 + 6069188 * 2 ^ 59
def prefixEnd_6069188 : Nat := 4983230072969 + 3 ^ 40 * 6069188 * 2
def baseEnd_6069188 : Nat := 3116410626499905507738319

theorem tailTrace_6069188 : CollatzResearch.WordTrace tailWord_6069188 prefixEnd_6069188 3116410626499905507738319 := by
  unfold tailWord_6069188
  simp only [CollatzResearch.WordTrace]
  refine ⟨110680735968187942816380109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147574314624250590421840145 110680735968187942816380109)
  ·
    refine ⟨41505275988070478556142541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110680735968187942816380109 41505275988070478556142541)
    ·
      refine ⟨15564478495526429458553453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41505275988070478556142541 15564478495526429458553453)
      ·
        refine ⟨5836679435822411046957545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15564478495526429458553453 5836679435822411046957545)
        ·
          refine ⟨4377509576866808285218159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5836679435822411046957545 4377509576866808285218159)
          ·
            refine ⟨6566264365300212427827239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377509576866808285218159 6566264365300212427827239)
            ·
              refine ⟨9849396547950318641740859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566264365300212427827239 9849396547950318641740859)
              ·
                refine ⟨14774094821925477962611289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9849396547950318641740859 14774094821925477962611289)
                ·
                  refine ⟨11080571116444108471958467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14774094821925477962611289 11080571116444108471958467)
                  ·
                    refine ⟨16620856674666162707937701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11080571116444108471958467 16620856674666162707937701)
                    ·
                      refine ⟨3116410626499905507738319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16620856674666162707937701 3116410626499905507738319)
                      ·
                        rfl

theorem cell23_6069188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_6069188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069188 prefixEnd_6069188 := by exact prefixLift 6069188
  have htrace : WordTrace (prefixWord ++ tailWord_6069188) baseStart_6069188 baseEnd_6069188 := by
    simpa [prefixWord, tailWord_6069188, baseEnd_6069188] using wordTrace_append hprefix tailTrace_6069188
  have hstable : (prefixWord ++ tailWord_6069188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069188).length < 2 ^ (prefixWord ++ tailWord_6069188).sum := by decide
  have hdescent : baseEnd_6069188 < baseStart_6069188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069244 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_6069244 : Nat := 118140960795 + 6069244 * 2 ^ 59
def prefixEnd_6069244 : Nat := 4983230072969 + 3 ^ 40 * 6069244 * 2
def baseEnd_6069244 : Nat := 3116439381416557288638061

theorem tailTrace_6069244 : CollatzResearch.WordTrace tailWord_6069244 prefixEnd_6069244 3116439381416557288638061 := by
  unfold tailWord_6069244
  simp only [CollatzResearch.WordTrace]
  refine ⟨110681757212086503598399393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147575676282782004797865857 110681757212086503598399393)
  ·
    refine ⟨83011317909064877698799545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110681757212086503598399393 83011317909064877698799545)
    ·
      refine ⟨62258488431798658274099659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83011317909064877698799545 62258488431798658274099659)
      ·
        refine ⟨93387732647697987411149489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62258488431798658274099659 93387732647697987411149489)
        ·
          refine ⟨70040799485773490558362117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93387732647697987411149489 70040799485773490558362117)
          ·
            refine ⟨13132649903582529479692897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70040799485773490558362117 13132649903582529479692897)
            ·
              refine ⟨9849487427686897109769673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13132649903582529479692897 9849487427686897109769673)
              ·
                refine ⟨7387115570765172832327255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9849487427686897109769673 7387115570765172832327255)
                ·
                  refine ⟨11080673356147759248490883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7387115570765172832327255 11080673356147759248490883)
                  ·
                    refine ⟨16621010034221638872736325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11080673356147759248490883 16621010034221638872736325)
                    ·
                      refine ⟨3116439381416557288638061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16621010034221638872736325 3116439381416557288638061)
                      ·
                        rfl

theorem cell23_6069244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_6069244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069244 prefixEnd_6069244 := by exact prefixLift 6069244
  have htrace : WordTrace (prefixWord ++ tailWord_6069244) baseStart_6069244 baseEnd_6069244 := by
    simpa [prefixWord, tailWord_6069244, baseEnd_6069244] using wordTrace_append hprefix tailTrace_6069244
  have hstable : (prefixWord ++ tailWord_6069244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069244).length < 2 ^ (prefixWord ++ tailWord_6069244).sum := by decide
  have hdescent : baseEnd_6069244 < baseStart_6069244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069294 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_6069294 : Nat := 118140960795 + 6069294 * 2 ^ 59
def prefixEnd_6069294 : Nat := 4983230072969 + 3 ^ 40 * 6069294 * 2
def baseEnd_6069294 : Nat := 3116465055449282093012831

theorem tailTrace_6069294 : CollatzResearch.WordTrace tailWord_6069294 prefixEnd_6069294 3116465055449282093012831 := by
  unfold tailWord_6069294
  simp only [CollatzResearch.WordTrace]
  refine ⟨27670667259248983217014867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147576892049327910490745957 27670667259248983217014867)
  ·
    refine ⟨41506000888873474825522301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27670667259248983217014867 41506000888873474825522301)
    ·
      refine ⟨15564750333327553059570863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41506000888873474825522301 15564750333327553059570863)
      ·
        refine ⟨23347125499991329589356295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15564750333327553059570863 23347125499991329589356295)
        ·
          refine ⟨35020688249986994384034443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23347125499991329589356295 35020688249986994384034443)
          ·
            refine ⟨52531032374980491576051665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35020688249986994384034443 52531032374980491576051665)
            ·
              refine ⟨39398274281235368682038749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52531032374980491576051665 39398274281235368682038749)
              ·
                refine ⟨14774352855463263255764531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39398274281235368682038749 14774352855463263255764531)
                ·
                  refine ⟨22161529283194894883646797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14774352855463263255764531 22161529283194894883646797)
                  ·
                    refine ⟨8310573481198085581367549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22161529283194894883646797 8310573481198085581367549)
                    ·
                      refine ⟨3116465055449282093012831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8310573481198085581367549 3116465055449282093012831)
                      ·
                        rfl

theorem cell23_6069294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_6069294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069294 prefixEnd_6069294 := by exact prefixLift 6069294
  have htrace : WordTrace (prefixWord ++ tailWord_6069294) baseStart_6069294 baseEnd_6069294 := by
    simpa [prefixWord, tailWord_6069294, baseEnd_6069294] using wordTrace_append hprefix tailTrace_6069294
  have hstable : (prefixWord ++ tailWord_6069294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069294).length < 2 ^ (prefixWord ++ tailWord_6069294).sum := by decide
  have hdescent : baseEnd_6069294 < baseStart_6069294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069351 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_6069351 : Nat := 118140960795 + 6069351 * 2 ^ 59
def prefixEnd_6069351 : Nat := 4983230072969 + 3 ^ 40 * 6069351 * 2
def baseEnd_6069351 : Nat := 3116494323846588370000069

theorem tailTrace_6069351 : CollatzResearch.WordTrace tailWord_6069351 prefixEnd_6069351 3116494323846588370000069 := by
  unfold tailWord_6069351
  simp only [CollatzResearch.WordTrace]
  refine ⟨221367417034785364470943907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147578278023190242980629271 221367417034785364470943907)
  ·
    refine ⟨332051125552178046706415861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221367417034785364470943907 332051125552178046706415861)
    ·
      refine ⟨31129793020516691878726487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 332051125552178046706415861 31129793020516691878726487)
      ·
        refine ⟨46694689530775037818089731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31129793020516691878726487 46694689530775037818089731)
        ·
          refine ⟨70042034296162556727134597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46694689530775037818089731 70042034296162556727134597)
          ·
            refine ⟨13132881430530479386337737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70042034296162556727134597 13132881430530479386337737)
            ·
              refine ⟨9849661072897859539753303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13132881430530479386337737 9849661072897859539753303)
              ·
                refine ⟨14774491609346789309629955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9849661072897859539753303 14774491609346789309629955)
                ·
                  refine ⟨22161737414020183964444933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14774491609346789309629955 22161737414020183964444933)
                  ·
                    refine ⟨4155325765128784493333425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22161737414020183964444933 4155325765128784493333425)
                    ·
                      refine ⟨3116494323846588370000069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4155325765128784493333425 3116494323846588370000069)
                      ·
                        rfl

theorem cell23_6069351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_6069351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069351 prefixEnd_6069351 := by exact prefixLift 6069351
  have htrace : WordTrace (prefixWord ++ tailWord_6069351) baseStart_6069351 baseEnd_6069351 := by
    simpa [prefixWord, tailWord_6069351, baseEnd_6069351] using wordTrace_append hprefix tailTrace_6069351
  have hstable : (prefixWord ++ tailWord_6069351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069351).length < 2 ^ (prefixWord ++ tailWord_6069351).sum := by decide
  have hdescent : baseEnd_6069351 < baseStart_6069351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069357 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 9]
def baseStart_6069357 : Nat := 118140960795 + 6069357 * 2 ^ 59
def prefixEnd_6069357 : Nat := 4983230072969 + 3 ^ 40 * 6069357 * 2
def baseEnd_6069357 : Nat := 346277489414501705169449

theorem tailTrace_6069357 : CollatzResearch.WordTrace tailWord_6069357 prefixEnd_6069357 346277489414501705169449 := by
  unfold tailWord_6069357
  simp only [CollatzResearch.WordTrace]
  refine ⟨221367635872763627495662325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147578423915175751663774883 221367635872763627495662325)
  ·
    refine ⟨20753215863071590077718343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221367635872763627495662325 20753215863071590077718343)
    ·
      refine ⟨31129823794607385116577515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20753215863071590077718343 31129823794607385116577515)
      ·
        refine ⟨46694735691911077674866273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31129823794607385116577515 46694735691911077674866273)
        ·
          refine ⟨35021051768933308256149705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46694735691911077674866273 35021051768933308256149705)
          ·
            refine ⟨26265788826699981192112279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35021051768933308256149705 26265788826699981192112279)
            ·
              refine ⟨39398683240049971788168419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26265788826699981192112279 39398683240049971788168419)
              ·
                refine ⟨59098024860074957682252629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39398683240049971788168419 59098024860074957682252629)
                ·
                  refine ⟨346277489414501705169449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59098024860074957682252629 346277489414501705169449)
                  ·
                    rfl

theorem cell23_6069357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_6069357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069357 prefixEnd_6069357 := by exact prefixLift 6069357
  have htrace : WordTrace (prefixWord ++ tailWord_6069357) baseStart_6069357 baseEnd_6069357 := by
    simpa [prefixWord, tailWord_6069357, baseEnd_6069357] using wordTrace_append hprefix tailTrace_6069357
  have hstable : (prefixWord ++ tailWord_6069357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069357).length < 2 ^ (prefixWord ++ tailWord_6069357).sum := by decide
  have hdescent : baseEnd_6069357 < baseStart_6069357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069367 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_6069367 : Nat := 118140960795 + 6069367 * 2 ^ 59
def prefixEnd_6069367 : Nat := 4983230072969 + 3 ^ 40 * 6069367 * 2
def baseEnd_6069367 : Nat := 3116502539537060307399995

theorem tailTrace_6069367 : CollatzResearch.WordTrace tailWord_6069367 prefixEnd_6069367 3116502539537060307399995 := by
  unfold tailWord_6069367
  simp only [CollatzResearch.WordTrace]
  refine ⟨221368000602727399203526355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147578667068484932802350903 221368000602727399203526355)
  ·
    refine ⟨332052000904091098805289533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221368000602727399203526355 332052000904091098805289533)
    ·
      refine ⟨124519500339034162051983575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332052000904091098805289533 124519500339034162051983575)
      ·
        refine ⟨186779250508551243077975363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124519500339034162051983575 186779250508551243077975363)
        ·
          refine ⟨280168875762826864616963045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186779250508551243077975363 280168875762826864616963045)
          ·
            refine ⟨52531664205530037115680571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280168875762826864616963045 52531664205530037115680571)
            ·
              refine ⟨78797496308295055673520857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52531664205530037115680571 78797496308295055673520857)
              ·
                refine ⟨59098122231221291755140643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78797496308295055673520857 59098122231221291755140643)
                ·
                  refine ⟨88647183346831937632710965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59098122231221291755140643 88647183346831937632710965)
                  ·
                    refine ⟨8310673438765494153066653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88647183346831937632710965 8310673438765494153066653)
                    ·
                      refine ⟨3116502539537060307399995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8310673438765494153066653 3116502539537060307399995)
                      ·
                        rfl

theorem cell23_6069367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_6069367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069367 prefixEnd_6069367 := by exact prefixLift 6069367
  have htrace : WordTrace (prefixWord ++ tailWord_6069367) baseStart_6069367 baseEnd_6069367 := by
    simpa [prefixWord, tailWord_6069367, baseEnd_6069367] using wordTrace_append hprefix tailTrace_6069367
  have hstable : (prefixWord ++ tailWord_6069367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069367).length < 2 ^ (prefixWord ++ tailWord_6069367).sum := by decide
  have hdescent : baseEnd_6069367 < baseStart_6069367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069387 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 2, 5]
def baseStart_6069387 : Nat := 118140960795 + 6069387 * 2 ^ 59
def prefixEnd_6069387 : Nat := 4983230072969 + 3 ^ 40 * 6069387 * 2
def baseEnd_6069387 : Nat := 1038837603050050076383301

theorem tailTrace_6069387 : CollatzResearch.WordTrace tailWord_6069387 prefixEnd_6069387 1038837603050050076383301 := by
  unfold tailWord_6069387
  simp only [CollatzResearch.WordTrace]
  refine ⟨221368730062654942619254415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147579153375103295079502943 221368730062654942619254415)
  ·
    refine ⟨332053095093982413928881623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221368730062654942619254415 332053095093982413928881623)
    ·
      refine ⟨498079642640973620893322435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332053095093982413928881623 498079642640973620893322435)
      ·
        refine ⟨747119463961460431339983653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498079642640973620893322435 747119463961460431339983653)
        ·
          refine ⟨140084899492773830876246935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 747119463961460431339983653 140084899492773830876246935)
          ·
            refine ⟨210127349239160746314370403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140084899492773830876246935 210127349239160746314370403)
            ·
              refine ⟨315191023858741119471555605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210127349239160746314370403 315191023858741119471555605)
              ·
                refine ⟨14774579243378489975229169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 315191023858741119471555605 14774579243378489975229169)
                ·
                  refine ⟨11080934432533867481421877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14774579243378489975229169 11080934432533867481421877)
                  ·
                    refine ⟨1038837603050050076383301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11080934432533867481421877 1038837603050050076383301)
                    ·
                      rfl

theorem cell23_6069387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 5].length) (baseStart_6069387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069387 prefixEnd_6069387 := by exact prefixLift 6069387
  have htrace : WordTrace (prefixWord ++ tailWord_6069387) baseStart_6069387 baseEnd_6069387 := by
    simpa [prefixWord, tailWord_6069387, baseEnd_6069387] using wordTrace_append hprefix tailTrace_6069387
  have hstable : (prefixWord ++ tailWord_6069387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069387).length < 2 ^ (prefixWord ++ tailWord_6069387).sum := by decide
  have hdescent : baseEnd_6069387 < baseStart_6069387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069437 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_6069437 : Nat := 118140960795 + 6069437 * 2 ^ 59
def prefixEnd_6069437 : Nat := 4983230072969 + 3 ^ 40 * 6069437 * 2
def baseEnd_6069437 : Nat := 3116538483182875033524673

theorem tailTrace_6069437 : CollatzResearch.WordTrace tailWord_6069437 prefixEnd_6069437 3116538483182875033524673 := by
  unfold tailWord_6069437
  simp only [CollatzResearch.WordTrace]
  refine ⟨221370553712473801158574565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147580369141649200772383043 221370553712473801158574565)
  ·
    refine ⟨41506978821088837717232731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221370553712473801158574565 41506978821088837717232731)
    ·
      refine ⟨62260468231633256575849097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41506978821088837717232731 62260468231633256575849097)
      ·
        refine ⟨46695351173724942431886823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62260468231633256575849097 46695351173724942431886823)
        ·
          refine ⟨70043026760587413647830235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46695351173724942431886823 70043026760587413647830235)
          ·
            refine ⟨105064540140881120471745353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70043026760587413647830235 105064540140881120471745353)
            ·
              refine ⟨78798405105660840353809015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105064540140881120471745353 78798405105660840353809015)
              ·
                refine ⟨118197607658491260530713523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78798405105660840353809015 118197607658491260530713523)
                ·
                  refine ⟨177296411487736890796070285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118197607658491260530713523 177296411487736890796070285)
                  ·
                    refine ⟨66486154307901334048526357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177296411487736890796070285 66486154307901334048526357)
                    ·
                      refine ⟨3116538483182875033524673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66486154307901334048526357 3116538483182875033524673)
                      ·
                        rfl

theorem cell23_6069437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_6069437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069437 prefixEnd_6069437 := by exact prefixLift 6069437
  have htrace : WordTrace (prefixWord ++ tailWord_6069437) baseStart_6069437 baseEnd_6069437 := by
    simpa [prefixWord, tailWord_6069437, baseEnd_6069437] using wordTrace_append hprefix tailTrace_6069437
  have hstable : (prefixWord ++ tailWord_6069437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069437).length < 2 ^ (prefixWord ++ tailWord_6069437).sum := by decide
  have hdescent : baseEnd_6069437 < baseStart_6069437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069441 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6069441 : Nat := 118140960795 + 6069441 * 2 ^ 59
def prefixEnd_6069441 : Nat := 4983230072969 + 3 ^ 40 * 6069441 * 2
def baseEnd_6069441 : Nat := 3116540537105493017874655

theorem tailTrace_6069441 : CollatzResearch.WordTrace tailWord_6069441 prefixEnd_6069441 3116540537105493017874655 := by
  unfold tailWord_6069441
  simp only [CollatzResearch.WordTrace]
  refine ⟨221370699604459309841720177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147580466402972873227813451 221370699604459309841720177)
  ·
    refine ⟨166028024703344482381290133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221370699604459309841720177 166028024703344482381290133)
    ·
      refine ⟨7782563657969272611622975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166028024703344482381290133 7782563657969272611622975)
      ·
        refine ⟨11673845486953908917434463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7782563657969272611622975 11673845486953908917434463)
        ·
          refine ⟨17510768230430863376151695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11673845486953908917434463 17510768230430863376151695)
          ·
            refine ⟨26266152345646295064227543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17510768230430863376151695 26266152345646295064227543)
            ·
              refine ⟨39399228518469442596341315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26266152345646295064227543 39399228518469442596341315)
              ·
                refine ⟨59098842777704163894511973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39399228518469442596341315 59098842777704163894511973)
                ·
                  refine ⟨11081033020819530730220995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59098842777704163894511973 11081033020819530730220995)
                  ·
                    refine ⟨16621549531229296095331493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11081033020819530730220995 16621549531229296095331493)
                    ·
                      refine ⟨3116540537105493017874655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16621549531229296095331493 3116540537105493017874655)
                      ·
                        rfl

theorem cell23_6069441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6069441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069441 prefixEnd_6069441 := by exact prefixLift 6069441
  have htrace : WordTrace (prefixWord ++ tailWord_6069441) baseStart_6069441 baseEnd_6069441 := by
    simpa [prefixWord, tailWord_6069441, baseEnd_6069441] using wordTrace_append hprefix tailTrace_6069441
  have hstable : (prefixWord ++ tailWord_6069441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069441).length < 2 ^ (prefixWord ++ tailWord_6069441).sum := by decide
  have hdescent : baseEnd_6069441 < baseStart_6069441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069442 : List Nat := [3, 5, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6069442 : Nat := 118140960795 + 6069442 * 2 ^ 59
def prefixEnd_6069442 : Nat := 4983230072969 + 3 ^ 40 * 6069442 * 2
def baseEnd_6069442 : Nat := 346282338954016390440239

theorem tailTrace_6069442 : CollatzResearch.WordTrace tailWord_6069442 prefixEnd_6069442 346282338954016390440239 := by
  unfold tailWord_6069442
  simp only [CollatzResearch.WordTrace]
  refine ⟨55342684019363921753126645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147580490718303791341671053 55342684019363921753126645)
  ·
    refine ⟨5188376626815367664355623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55342684019363921753126645 5188376626815367664355623)
    ·
      refine ⟨7782564940223051496533435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5188376626815367664355623 7782564940223051496533435)
      ·
        refine ⟨11673847410334577244800153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7782564940223051496533435 11673847410334577244800153)
        ·
          refine ⟨8755385557750932933600115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11673847410334577244800153 8755385557750932933600115)
          ·
            refine ⟨13133078336626399400400173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8755385557750932933600115 13133078336626399400400173)
            ·
              refine ⟨4924904376234899775150065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13133078336626399400400173 4924904376234899775150065)
              ·
                refine ⟨3693678282176174831362549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924904376234899775150065 3693678282176174831362549)
                ·
                  refine ⟨346282338954016390440239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3693678282176174831362549 346282338954016390440239)
                  ·
                    rfl

theorem cell23_6069442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6069442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069442 prefixEnd_6069442 := by exact prefixLift 6069442
  have htrace : WordTrace (prefixWord ++ tailWord_6069442) baseStart_6069442 baseEnd_6069442 := by
    simpa [prefixWord, tailWord_6069442, baseEnd_6069442] using wordTrace_append hprefix tailTrace_6069442
  have hstable : (prefixWord ++ tailWord_6069442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069442).length < 2 ^ (prefixWord ++ tailWord_6069442).sum := by decide
  have hdescent : baseEnd_6069442 < baseStart_6069442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069502 : List Nat := [4, 2, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_6069502 : Nat := 118140960795 + 6069502 * 2 ^ 59
def prefixEnd_6069502 : Nat := 4983230072969 + 3 ^ 40 * 6069502 * 2
def baseEnd_6069502 : Nat := 1038857286475139093070625

theorem tailTrace_6069502 : CollatzResearch.WordTrace tailWord_6069502 prefixEnd_6069502 1038857286475139093070625 := by
  unfold tailWord_6069502
  simp only [CollatzResearch.WordTrace]
  refine ⟨27671615557154789657461345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147581949638158878173127173 27671615557154789657461345)
  ·
    refine ⟨20753711667866092243096009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27671615557154789657461345 20753711667866092243096009)
    ·
      refine ⟨15565283750899569182322007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20753711667866092243096009 15565283750899569182322007)
      ·
        refine ⟨23347925626349353773483011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15565283750899569182322007 23347925626349353773483011)
        ·
          refine ⟨35021888439524030660224517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23347925626349353773483011 35021888439524030660224517)
          ·
            refine ⟨6566604082410755748792097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35021888439524030660224517 6566604082410755748792097)
            ·
              refine ⟨4924953061808066811594073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6566604082410755748792097 4924953061808066811594073)
              ·
                refine ⟨3693714796356050108695555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924953061808066811594073 3693714796356050108695555)
                ·
                  refine ⟨5540572194534075163043333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693714796356050108695555 5540572194534075163043333)
                  ·
                    refine ⟨1038857286475139093070625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5540572194534075163043333 1038857286475139093070625)
                    ·
                      rfl

theorem cell23_6069502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_6069502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069502 prefixEnd_6069502 := by exact prefixLift 6069502
  have htrace : WordTrace (prefixWord ++ tailWord_6069502) baseStart_6069502 baseEnd_6069502 := by
    simpa [prefixWord, tailWord_6069502, baseEnd_6069502] using wordTrace_append hprefix tailTrace_6069502
  have hstable : (prefixWord ++ tailWord_6069502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069502).length < 2 ^ (prefixWord ++ tailWord_6069502).sum := by decide
  have hdescent : baseEnd_6069502 < baseStart_6069502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069535 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 2, 3, 2]
def baseStart_6069535 : Nat := 118140960795 + 6069535 * 2 ^ 59
def prefixEnd_6069535 : Nat := 4983230072969 + 3 ^ 40 * 6069535 * 2
def baseEnd_6069535 : Nat := 3116588804287015650099223

theorem tailTrace_6069535 : CollatzResearch.WordTrace tailWord_6069535 prefixEnd_6069535 3116588804287015650099223 := by
  unfold tailWord_6069535
  simp only [CollatzResearch.WordTrace]
  refine ⟨221374128066118763895642059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147582752044079175930428039 221374128066118763895642059)
  ·
    refine ⟨332061192099178145843463089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221374128066118763895642059 332061192099178145843463089)
    ·
      refine ⟨249045894074383609382597317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332061192099178145843463089 249045894074383609382597317)
      ·
        refine ⟨46696105138946926759236997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249045894074383609382597317 46696105138946926759236997)
        ·
          refine ⟨8755519713552548767356937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46696105138946926759236997 8755519713552548767356937)
          ·
            refine ⟨6566639785164411575517703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8755519713552548767356937 6566639785164411575517703)
            ·
              refine ⟨9849959677746617363276555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566639785164411575517703 9849959677746617363276555)
              ·
                refine ⟨14774939516619926044914833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9849959677746617363276555 14774939516619926044914833)
                ·
                  refine ⟨11081204637464944533686125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14774939516619926044914833 11081204637464944533686125)
                  ·
                    refine ⟨4155451739049354200132297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11081204637464944533686125 4155451739049354200132297)
                    ·
                      refine ⟨3116588804287015650099223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4155451739049354200132297 3116588804287015650099223)
                      ·
                        rfl

theorem cell23_6069535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_6069535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069535 prefixEnd_6069535 := by exact prefixLift 6069535
  have htrace : WordTrace (prefixWord ++ tailWord_6069535) baseStart_6069535 baseEnd_6069535 := by
    simpa [prefixWord, tailWord_6069535, baseEnd_6069535] using wordTrace_append hprefix tailTrace_6069535
  have hstable : (prefixWord ++ tailWord_6069535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069535).length < 2 ^ (prefixWord ++ tailWord_6069535).sum := by decide
  have hdescent : baseEnd_6069535 < baseStart_6069535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069554 : List Nat := [3, 2, 1, 1, 4, 2, 10]
def baseStart_6069554 : Nat := 118140960795 + 6069554 * 2 ^ 59
def prefixEnd_6069554 : Nat := 4983230072969 + 3 ^ 40 * 6069554 * 2
def baseEnd_6069554 : Nat := 38476525437277173774835

theorem tailTrace_6069554 : CollatzResearch.WordTrace tailWord_6069554 prefixEnd_6069554 38476525437277173774835 := by
  unfold tailWord_6069554
  simp only [CollatzResearch.WordTrace]
  refine ⟨55343705263262482535145929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147583214035366620093722477 55343705263262482535145929)
  ·
    refine ⟨41507778947446861901359447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55343705263262482535145929 41507778947446861901359447)
    ·
      refine ⟨62261668421170292852039171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41507778947446861901359447 62261668421170292852039171)
      ·
        refine ⟨93392502631755439278058757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62261668421170292852039171 93392502631755439278058757)
        ·
          refine ⟨17511094243454144864636017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93392502631755439278058757 17511094243454144864636017)
          ·
            refine ⟨13133320682590608648477013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17511094243454144864636017 13133320682590608648477013)
            ·
              refine ⟨38476525437277173774835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13133320682590608648477013 38476525437277173774835)
              ·
                rfl

theorem cell23_6069554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 10].length) (baseStart_6069554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069554 prefixEnd_6069554 := by exact prefixLift 6069554
  have htrace : WordTrace (prefixWord ++ tailWord_6069554) baseStart_6069554 baseEnd_6069554 := by
    simpa [prefixWord, tailWord_6069554, baseEnd_6069554] using wordTrace_append hprefix tailTrace_6069554
  have hstable : (prefixWord ++ tailWord_6069554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069554).length < 2 ^ (prefixWord ++ tailWord_6069554).sum := by decide
  have hdescent : baseEnd_6069554 < baseStart_6069554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069594 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_6069594 : Nat := 118140960795 + 6069594 * 2 ^ 59
def prefixEnd_6069594 : Nat := 4983230072969 + 3 ^ 40 * 6069594 * 2
def baseEnd_6069594 : Nat := 3116619099645630919261451

theorem tailTrace_6069594 : CollatzResearch.WordTrace tailWord_6069594 prefixEnd_6069594 3116619099645630919261451 := by
  unfold tailWord_6069594
  simp only [CollatzResearch.WordTrace]
  refine ⟨55344069993226254243009959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147584186648603344648026557 55344069993226254243009959)
  ·
    refine ⟨83016104989839381364514939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55344069993226254243009959 83016104989839381364514939)
    ·
      refine ⟨124524157484759072046772409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83016104989839381364514939 124524157484759072046772409)
      ·
        refine ⟨93393118113569304035079307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124524157484759072046772409 93393118113569304035079307)
        ·
          refine ⟨140089677170353956052618961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93393118113569304035079307 140089677170353956052618961)
          ·
            refine ⟨105067257877765467039464221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140089677170353956052618961 105067257877765467039464221)
            ·
              refine ⟨39400221704162050139799083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105067257877765467039464221 39400221704162050139799083)
              ·
                refine ⟨59100332556243075209698625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39400221704162050139799083 59100332556243075209698625)
                ·
                  refine ⟨44325249417182306407273969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59100332556243075209698625 44325249417182306407273969)
                  ·
                    refine ⟨33243937062886729805455477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44325249417182306407273969 33243937062886729805455477)
                    ·
                      refine ⟨3116619099645630919261451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33243937062886729805455477 3116619099645630919261451)
                      ·
                        rfl

theorem cell23_6069594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_6069594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069594 prefixEnd_6069594 := by exact prefixLift 6069594
  have htrace : WordTrace (prefixWord ++ tailWord_6069594) baseStart_6069594 baseEnd_6069594 := by
    simpa [prefixWord, tailWord_6069594, baseEnd_6069594] using wordTrace_append hprefix tailTrace_6069594
  have hstable : (prefixWord ++ tailWord_6069594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069594).length < 2 ^ (prefixWord ++ tailWord_6069594).sum := by decide
  have hdescent : baseEnd_6069594 < baseStart_6069594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069644 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 9]
def baseStart_6069644 : Nat := 118140960795 + 6069644 * 2 ^ 59
def prefixEnd_6069644 : Nat := 4983230072969 + 3 ^ 40 * 6069644 * 2
def baseEnd_6069644 : Nat := 346293863742039524848469

theorem tailTrace_6069644 : CollatzResearch.WordTrace tailWord_6069644 prefixEnd_6069644 346293863742039524848469 := by
  unfold tailWord_6069644
  simp only [CollatzResearch.WordTrace]
  refine ⟨110689051811361937755679993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147585402415149250340906657 110689051811361937755679993)
  ·
    refine ⟨83016788858521453316759995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110689051811361937755679993 83016788858521453316759995)
    ·
      refine ⟨124525183287782179975139993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83016788858521453316759995 124525183287782179975139993)
      ·
        refine ⟨93393887465836634981354995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124525183287782179975139993 93393887465836634981354995)
        ·
          refine ⟨140090831198754952472032493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93393887465836634981354995 140090831198754952472032493)
          ·
            refine ⟨52534061699533107177012185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140090831198754952472032493 52534061699533107177012185)
            ·
              refine ⟨39400546274649830382759139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52534061699533107177012185 39400546274649830382759139)
              ·
                refine ⟨59100819411974745574138709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39400546274649830382759139 59100819411974745574138709)
                ·
                  refine ⟨346293863742039524848469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59100819411974745574138709 346293863742039524848469)
                  ·
                    rfl

theorem cell23_6069644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_6069644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069644 prefixEnd_6069644 := by exact prefixLift 6069644
  have htrace : WordTrace (prefixWord ++ tailWord_6069644) baseStart_6069644 baseEnd_6069644 := by
    simpa [prefixWord, tailWord_6069644, baseEnd_6069644] using wordTrace_append hprefix tailTrace_6069644
  have hstable : (prefixWord ++ tailWord_6069644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069644).length < 2 ^ (prefixWord ++ tailWord_6069644).sum := by decide
  have hdescent : baseEnd_6069644 < baseStart_6069644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069708 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_6069708 : Nat := 118140960795 + 6069708 * 2 ^ 59
def prefixEnd_6069708 : Nat := 4983230072969 + 3 ^ 40 * 6069708 * 2
def baseEnd_6069708 : Nat := 1038892545480081157745309

theorem tailTrace_6069708 : CollatzResearch.WordTrace tailWord_6069708 prefixEnd_6069708 1038892545480081157745309 := by
  unfold tailWord_6069708
  simp only [CollatzResearch.WordTrace]
  refine ⟨110690218947246007220844889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147586958596328009627793185 110690218947246007220844889)
  ·
    refine ⟨83017664210434505415633667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110690218947246007220844889 83017664210434505415633667)
    ·
      refine ⟨124526496315651758123450501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83017664210434505415633667 124526496315651758123450501)
      ·
        refine ⟨23348718059184704648146969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124526496315651758123450501 23348718059184704648146969)
        ·
          refine ⟨17511538544388528486110227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23348718059184704648146969 17511538544388528486110227)
          ·
            refine ⟨26267307816582792729165341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17511538544388528486110227 26267307816582792729165341)
            ·
              refine ⟨9850240431218547273437003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26267307816582792729165341 9850240431218547273437003)
              ·
                refine ⟨14775360646827820910155505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9850240431218547273437003 14775360646827820910155505)
                ·
                  refine ⟨11081520485120865682616629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14775360646827820910155505 11081520485120865682616629)
                  ·
                    refine ⟨1038892545480081157745309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11081520485120865682616629 1038892545480081157745309)
                    ·
                      rfl

theorem cell23_6069708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_6069708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069708 prefixEnd_6069708 := by exact prefixLift 6069708
  have htrace : WordTrace (prefixWord ++ tailWord_6069708) baseStart_6069708 baseEnd_6069708 := by
    simpa [prefixWord, tailWord_6069708, baseEnd_6069708] using wordTrace_append hprefix tailTrace_6069708
  have hstable : (prefixWord ++ tailWord_6069708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069708).length < 2 ^ (prefixWord ++ tailWord_6069708).sum := by decide
  have hdescent : baseEnd_6069708 < baseStart_6069708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069815 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 1, 5]
def baseStart_6069815 : Nat := 118140960795 + 6069815 * 2 ^ 59
def prefixEnd_6069815 : Nat := 4983230072969 + 3 ^ 40 * 6069815 * 2
def baseEnd_6069815 : Nat := 1038910859623424851532645

theorem tailTrace_6069815 : CollatzResearch.WordTrace tailWord_6069815 prefixEnd_6069815 1038910859623424851532645 := by
  unfold tailWord_6069815
  simp only [CollatzResearch.WordTrace]
  refine ⟨221384340505104371715834899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147589560336736247810556599 221384340505104371715834899)
  ·
    refine ⟨332076510757656557573752349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221384340505104371715834899 332076510757656557573752349)
    ·
      refine ⟨124528691534121209090157131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332076510757656557573752349 124528691534121209090157131)
      ·
        refine ⟨186793037301181813635235697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124528691534121209090157131 186793037301181813635235697)
        ·
          refine ⟨140094777975886360226426773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186793037301181813635235697 140094777975886360226426773)
          ·
            refine ⟨6566942717619673135613755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140094777975886360226426773 6566942717619673135613755)
            ·
              refine ⟨9850414076429509703420633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6566942717619673135613755 9850414076429509703420633)
              ·
                refine ⟨7387810557322132277565475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9850414076429509703420633 7387810557322132277565475)
                ·
                  refine ⟨11081715835983198416348213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7387810557322132277565475 11081715835983198416348213)
                  ·
                    refine ⟨1038910859623424851532645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11081715835983198416348213 1038910859623424851532645)
                    ·
                      rfl

theorem cell23_6069815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_6069815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069815 prefixEnd_6069815 := by exact prefixLift 6069815
  have htrace : WordTrace (prefixWord ++ tailWord_6069815) baseStart_6069815 baseEnd_6069815 := by
    simpa [prefixWord, tailWord_6069815, baseEnd_6069815] using wordTrace_append hprefix tailTrace_6069815
  have hstable : (prefixWord ++ tailWord_6069815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069815).length < 2 ^ (prefixWord ++ tailWord_6069815).sum := by decide
  have hdescent : baseEnd_6069815 < baseStart_6069815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069818 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_6069818 : Nat := 118140960795 + 6069818 * 2 ^ 59
def prefixEnd_6069818 : Nat := 4983230072969 + 3 ^ 40 * 6069818 * 2
def baseEnd_6069818 : Nat := 3116734119312238042860421

theorem tailTrace_6069818 : CollatzResearch.WordTrace tailWord_6069818 prefixEnd_6069818 3116734119312238042860421 := by
  unfold tailWord_6069818
  simp only [CollatzResearch.WordTrace]
  refine ⟨55346112481023375807048527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147589633282729002152129405 55346112481023375807048527)
  ·
    refine ⟨83019168721535063710572791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55346112481023375807048527 83019168721535063710572791)
    ·
      refine ⟨124528753082302595565859187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83019168721535063710572791 124528753082302595565859187)
      ·
        refine ⟨186793129623453893348788781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124528753082302595565859187 186793129623453893348788781)
        ·
          refine ⟨70047423608795210005795793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186793129623453893348788781 70047423608795210005795793)
          ·
            refine ⟨52535567706596407504346845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70047423608795210005795793 52535567706596407504346845)
            ·
              refine ⟨19700837889973652814130067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52535567706596407504346845 19700837889973652814130067)
              ·
                refine ⟨29551256834960479221195101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19700837889973652814130067 29551256834960479221195101)
                ·
                  refine ⟨11081721313110179707948163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29551256834960479221195101 11081721313110179707948163)
                  ·
                    refine ⟨16622581969665269561922245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11081721313110179707948163 16622581969665269561922245)
                    ·
                      refine ⟨3116734119312238042860421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16622581969665269561922245 3116734119312238042860421)
                      ·
                        rfl

theorem cell23_6069818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_6069818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069818 prefixEnd_6069818 := by exact prefixLift 6069818
  have htrace : WordTrace (prefixWord ++ tailWord_6069818) baseStart_6069818 baseEnd_6069818 := by
    simpa [prefixWord, tailWord_6069818, baseEnd_6069818] using wordTrace_append hprefix tailTrace_6069818
  have hstable : (prefixWord ++ tailWord_6069818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069818).length < 2 ^ (prefixWord ++ tailWord_6069818).sum := by decide
  have hdescent : baseEnd_6069818 < baseStart_6069818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069869 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_6069869 : Nat := 118140960795 + 6069869 * 2 ^ 59
def prefixEnd_6069869 : Nat := 4983230072969 + 3 ^ 40 * 6069869 * 2
def baseEnd_6069869 : Nat := 3116760306825617343322687

theorem tailTrace_6069869 : CollatzResearch.WordTrace tailWord_6069869 prefixEnd_6069869 3116760306825617343322687 := by
  unfold tailWord_6069869
  simp only [CollatzResearch.WordTrace]
  refine ⟨221386310046908738938300661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147590873364605825958867107 221386310046908738938300661)
  ·
    refine ⟨20754966566897694275465687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221386310046908738938300661 20754966566897694275465687)
    ·
      refine ⟨31132449850346541413198531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20754966566897694275465687 31132449850346541413198531)
      ·
        refine ⟨46698674775519812119797797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31132449850346541413198531 46698674775519812119797797)
        ·
          refine ⟨8756001520409964772462087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46698674775519812119797797 8756001520409964772462087)
          ·
            refine ⟨13134002280614947158693131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8756001520409964772462087 13134002280614947158693131)
            ·
              refine ⟨19701003420922420738039697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134002280614947158693131 19701003420922420738039697)
              ·
                refine ⟨14775752565691815553529773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19701003420922420738039697 14775752565691815553529773)
                ·
                  refine ⟨5540907212134430832573665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14775752565691815553529773 5540907212134430832573665)
                  ·
                    refine ⟨4155680409100823124430249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5540907212134430832573665 4155680409100823124430249)
                    ·
                      refine ⟨3116760306825617343322687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4155680409100823124430249 3116760306825617343322687)
                      ·
                        rfl

theorem cell23_6069869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_6069869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069869 prefixEnd_6069869 := by exact prefixLift 6069869
  have htrace : WordTrace (prefixWord ++ tailWord_6069869) baseStart_6069869 baseEnd_6069869 := by
    simpa [prefixWord, tailWord_6069869, baseEnd_6069869] using wordTrace_append hprefix tailTrace_6069869
  have hstable : (prefixWord ++ tailWord_6069869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069869).length < 2 ^ (prefixWord ++ tailWord_6069869).sum := by decide
  have hdescent : baseEnd_6069869 < baseStart_6069869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069871 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 4, 7]
def baseStart_6069871 : Nat := 118140960795 + 6069871 * 2 ^ 59
def prefixEnd_6069871 : Nat := 4983230072969 + 3 ^ 40 * 6069871 * 2
def baseEnd_6069871 : Nat := 1038920444595642111832559

theorem tailTrace_6069871 : CollatzResearch.WordTrace tailWord_6069871 prefixEnd_6069871 1038920444595642111832559 := by
  unfold tailWord_6069871
  simp only [CollatzResearch.WordTrace]
  refine ⟨221386382992901493279873467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147590921995267662186582311 221386382992901493279873467)
  ·
    refine ⟨332079574489352239919810201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221386382992901493279873467 332079574489352239919810201)
    ·
      refine ⟨249059680867014179939857651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332079574489352239919810201 249059680867014179939857651)
      ·
        refine ⟨373589521300521269909786477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249059680867014179939857651 373589521300521269909786477)
        ·
          refine ⟨140096070487695476216169929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373589521300521269909786477 140096070487695476216169929)
          ·
            refine ⟨105072052865771607162127447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140096070487695476216169929 105072052865771607162127447)
            ·
              refine ⟨157608079298657410743191171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105072052865771607162127447 157608079298657410743191171)
              ·
                refine ⟨236412118947986116114786757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157608079298657410743191171 236412118947986116114786757)
                ·
                  refine ⟨44327272302747396771522517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236412118947986116114786757 44327272302747396771522517)
                  ·
                    refine ⟨1038920444595642111832559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44327272302747396771522517 1038920444595642111832559)
                    ·
                      rfl

theorem cell23_6069871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_6069871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069871 prefixEnd_6069871 := by exact prefixLift 6069871
  have htrace : WordTrace (prefixWord ++ tailWord_6069871) baseStart_6069871 baseEnd_6069871 := by
    simpa [prefixWord, tailWord_6069871, baseEnd_6069871] using wordTrace_append hprefix tailTrace_6069871
  have hstable : (prefixWord ++ tailWord_6069871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069871).length < 2 ^ (prefixWord ++ tailWord_6069871).sum := by decide
  have hdescent : baseEnd_6069871 < baseStart_6069871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069885 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_6069885 : Nat := 118140960795 + 6069885 * 2 ^ 59
def prefixEnd_6069885 : Nat := 4983230072969 + 3 ^ 40 * 6069885 * 2
def baseEnd_6069885 : Nat := 3116768522516089280722613

theorem tailTrace_6069885 : CollatzResearch.WordTrace tailWord_6069885 prefixEnd_6069885 3116768522516089280722613 := by
  unfold tailWord_6069885
  simp only [CollatzResearch.WordTrace]
  refine ⟨221386893614850773670883109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147591262409900515780588739 221386893614850773670883109)
  ·
    refine ⟨41510042552784520063290583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221386893614850773670883109 41510042552784520063290583)
    ·
      refine ⟨62265063829176780094935875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41510042552784520063290583 62265063829176780094935875)
      ·
        refine ⟨93397595743765170142403813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62265063829176780094935875 93397595743765170142403813)
        ·
          refine ⟨17512049201955969401700715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93397595743765170142403813 17512049201955969401700715)
          ·
            refine ⟨26268073802933954102551073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17512049201955969401700715 26268073802933954102551073)
            ·
              refine ⟨19701055352200465576913305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26268073802933954102551073 19701055352200465576913305)
              ·
                refine ⟨14775791514150349182684979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19701055352200465576913305 14775791514150349182684979)
                ·
                  refine ⟨22163687271225523774027469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14775791514150349182684979 22163687271225523774027469)
                  ·
                    refine ⟨8311382726709571415260301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22163687271225523774027469 8311382726709571415260301)
                    ·
                      refine ⟨3116768522516089280722613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8311382726709571415260301 3116768522516089280722613)
                      ·
                        rfl

theorem cell23_6069885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_6069885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069885 prefixEnd_6069885 := by exact prefixLift 6069885
  have htrace : WordTrace (prefixWord ++ tailWord_6069885) baseStart_6069885 baseEnd_6069885 := by
    simpa [prefixWord, tailWord_6069885, baseEnd_6069885] using wordTrace_append hprefix tailTrace_6069885
  have hstable : (prefixWord ++ tailWord_6069885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069885).length < 2 ^ (prefixWord ++ tailWord_6069885).sum := by decide
  have hdescent : baseEnd_6069885 < baseStart_6069885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069889 : List Nat := [1, 2, 4, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_6069889 : Nat := 118140960795 + 6069889 * 2 ^ 59
def prefixEnd_6069889 : Nat := 4983230072969 + 3 ^ 40 * 6069889 * 2
def baseEnd_6069889 : Nat := 3116770576438707265072595

theorem tailTrace_6069889 : CollatzResearch.WordTrace tailWord_6069889 prefixEnd_6069889 3116770576438707265072595 := by
  unfold tailWord_6069889
  simp only [CollatzResearch.WordTrace]
  refine ⟨221387039506836282354028721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147591359671224188236019147 221387039506836282354028721)
  ·
    refine ⟨166040279630127211765521541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221387039506836282354028721 166040279630127211765521541)
    ·
      refine ⟨31132552430648852206035289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166040279630127211765521541 31132552430648852206035289)
      ·
        refine ⟨23349414322986639154526467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31132552430648852206035289 23349414322986639154526467)
        ·
          refine ⟨35024121484479958731789701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23349414322986639154526467 35024121484479958731789701)
          ·
            refine ⟨6567022778339992262210569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35024121484479958731789701 6567022778339992262210569)
            ·
              refine ⟨4925267083754994196657927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6567022778339992262210569 4925267083754994196657927)
              ·
                refine ⟨7387900625632491294986891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4925267083754994196657927 7387900625632491294986891)
                ·
                  refine ⟨11081850938448736942480337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7387900625632491294986891 11081850938448736942480337)
                  ·
                    refine ⟨8311388203836552706860253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11081850938448736942480337 8311388203836552706860253)
                    ·
                      refine ⟨3116770576438707265072595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8311388203836552706860253 3116770576438707265072595)
                      ·
                        rfl

theorem cell23_6069889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_6069889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069889 prefixEnd_6069889 := by exact prefixLift 6069889
  have htrace : WordTrace (prefixWord ++ tailWord_6069889) baseStart_6069889 baseEnd_6069889 := by
    simpa [prefixWord, tailWord_6069889, baseEnd_6069889] using wordTrace_append hprefix tailTrace_6069889
  have hstable : (prefixWord ++ tailWord_6069889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069889).length < 2 ^ (prefixWord ++ tailWord_6069889).sum := by decide
  have hdescent : baseEnd_6069889 < baseStart_6069889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069896 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 2, 4]
def baseStart_6069896 : Nat := 118140960795 + 6069896 * 2 ^ 59
def prefixEnd_6069896 : Nat := 4983230072969 + 3 ^ 40 * 6069896 * 2
def baseEnd_6069896 : Nat := 1038924723601096245895021

theorem tailTrace_6069896 : CollatzResearch.WordTrace tailWord_6069896 prefixEnd_6069896 1038924723601096245895021 := by
  unfold tailWord_6069896
  simp only [CollatzResearch.WordTrace]
  refine ⟨110693647408905461274766771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147591529878540615033022361 110693647408905461274766771)
  ·
    refine ⟨166040471113358191912150157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110693647408905461274766771 166040471113358191912150157)
    ·
      refine ⟨62265176667509321967056309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166040471113358191912150157 62265176667509321967056309)
      ·
        refine ⟨5837360312578998934411529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62265176667509321967056309 5837360312578998934411529)
        ·
          refine ⟨4378020234434249200808647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5837360312578998934411529 4378020234434249200808647)
          ·
            refine ⟨6567030351651373801212971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378020234434249200808647 6567030351651373801212971)
            ·
              refine ⟨9850545527477060701819457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6567030351651373801212971 9850545527477060701819457)
              ·
                refine ⟨7387909145607795526364593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9850545527477060701819457 7387909145607795526364593)
                ·
                  refine ⟨5540931859205846644773445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7387909145607795526364593 5540931859205846644773445)
                  ·
                    refine ⟨1038924723601096245895021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5540931859205846644773445 1038924723601096245895021)
                    ·
                      rfl

theorem cell23_6069896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_6069896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069896 prefixEnd_6069896 := by exact prefixLift 6069896
  have htrace : WordTrace (prefixWord ++ tailWord_6069896) baseStart_6069896 baseEnd_6069896 := by
    simpa [prefixWord, tailWord_6069896, baseEnd_6069896] using wordTrace_append hprefix tailTrace_6069896
  have hstable : (prefixWord ++ tailWord_6069896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069896).length < 2 ^ (prefixWord ++ tailWord_6069896).sum := by decide
  have hdescent : baseEnd_6069896 < baseStart_6069896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069902 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_6069902 : Nat := 118140960795 + 6069902 * 2 ^ 59
def prefixEnd_6069902 : Nat := 4983230072969 + 3 ^ 40 * 6069902 * 2
def baseEnd_6069902 : Nat := 3116777251687215714210035

theorem tailTrace_6069902 : CollatzResearch.WordTrace tailWord_6069902 prefixEnd_6069902 3116777251687215714210035 := by
  unfold tailWord_6069902
  simp only [CollatzResearch.WordTrace]
  refine ⟨27673439206973648196781495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147591675770526123716167973 27673439206973648196781495)
  ·
    refine ⟨41510158810460472295172243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27673439206973648196781495 41510158810460472295172243)
    ·
      refine ⟨62265238215690708442758365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41510158810460472295172243 62265238215690708442758365)
      ·
        refine ⟨23349464330884015666034387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62265238215690708442758365 23349464330884015666034387)
        ·
          refine ⟨35024196496326023499051581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23349464330884015666034387 35024196496326023499051581)
          ·
            refine ⟨13134073686122258812144343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35024196496326023499051581 13134073686122258812144343)
            ·
              refine ⟨19701110529183388218216515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134073686122258812144343 19701110529183388218216515)
              ·
                refine ⟨29551665793775082327324773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19701110529183388218216515 29551665793775082327324773)
                ·
                  refine ⟨5540937336332827936373395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29551665793775082327324773 5540937336332827936373395)
                  ·
                    refine ⟨8311406004499241904560093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5540937336332827936373395 8311406004499241904560093)
                    ·
                      refine ⟨3116777251687215714210035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8311406004499241904560093 3116777251687215714210035)
                      ·
                        rfl

theorem cell23_6069902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_6069902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069902 prefixEnd_6069902 := by exact prefixLift 6069902
  have htrace : WordTrace (prefixWord ++ tailWord_6069902) baseStart_6069902 baseEnd_6069902 := by
    simpa [prefixWord, tailWord_6069902, baseEnd_6069902] using wordTrace_append hprefix tailTrace_6069902
  have hstable : (prefixWord ++ tailWord_6069902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069902).length < 2 ^ (prefixWord ++ tailWord_6069902).sum := by decide
  have hdescent : baseEnd_6069902 < baseStart_6069902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069919 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6069919 : Nat := 118140960795 + 6069919 * 2 ^ 59
def prefixEnd_6069919 : Nat := 4983230072969 + 3 ^ 40 * 6069919 * 2
def baseEnd_6069919 : Nat := 3116785980858342147697457

theorem tailTrace_6069919 : CollatzResearch.WordTrace tailWord_6069919 prefixEnd_6069919 3116785980858342147697457 := by
  unfold tailWord_6069919
  simp only [CollatzResearch.WordTrace]
  refine ⟨221388133696727597477620811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147592089131151731651747207 221388133696727597477620811)
  ·
    refine ⟨332082200545091396216431217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221388133696727597477620811 332082200545091396216431217)
    ·
      refine ⟨249061650408818547162323413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332082200545091396216431217 249061650408818547162323413)
      ·
        refine ⟨5837382431456684699116955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 249061650408818547162323413 5837382431456684699116955)
        ·
          refine ⟨8756073647185027048675433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5837382431456684699116955 8756073647185027048675433)
          ·
            refine ⟨6567055235388770286506575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8756073647185027048675433 6567055235388770286506575)
            ·
              refine ⟨9850582853083155429759863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6567055235388770286506575 9850582853083155429759863)
              ·
                refine ⟨14775874279624733144639795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9850582853083155429759863 14775874279624733144639795)
                ·
                  refine ⟨22163811419437099716959693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14775874279624733144639795 22163811419437099716959693)
                  ·
                    refine ⟨8311429282288912393859885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22163811419437099716959693 8311429282288912393859885)
                    ·
                      refine ⟨3116785980858342147697457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8311429282288912393859885 3116785980858342147697457)
                      ·
                        rfl

theorem cell23_6069919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6069919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069919 prefixEnd_6069919 := by exact prefixLift 6069919
  have htrace : WordTrace (prefixWord ++ tailWord_6069919) baseStart_6069919 baseEnd_6069919 := by
    simpa [prefixWord, tailWord_6069919, baseEnd_6069919] using wordTrace_append hprefix tailTrace_6069919
  have hstable : (prefixWord ++ tailWord_6069919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069919).length < 2 ^ (prefixWord ++ tailWord_6069919).sum := by decide
  have hdescent : baseEnd_6069919 < baseStart_6069919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069938 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_6069938 : Nat := 118140960795 + 6069938 * 2 ^ 59
def prefixEnd_6069938 : Nat := 4983230072969 + 3 ^ 40 * 6069938 * 2
def baseEnd_6069938 : Nat := 3116795736990777573359869

theorem tailTrace_6069938 : CollatzResearch.WordTrace tailWord_6069938 prefixEnd_6069938 3116795736990777573359869 := by
  unfold tailWord_6069938
  simp only [CollatzResearch.WordTrace]
  refine ⟨55347206670914690930640617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147592551122439175815041645 55347206670914690930640617)
  ·
    refine ⟨41510405003186018197980463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55347206670914690930640617 41510405003186018197980463)
    ·
      refine ⟨62265607504779027296970695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41510405003186018197980463 62265607504779027296970695)
      ·
        refine ⟨93398411257168540945456043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62265607504779027296970695 93398411257168540945456043)
        ·
          refine ⟨140097616885752811418184065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93398411257168540945456043 140097616885752811418184065)
          ·
            refine ⟨105073212664314608563638049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140097616885752811418184065 105073212664314608563638049)
            ·
              refine ⟨78804909498235956422728537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105073212664314608563638049 78804909498235956422728537)
              ·
                refine ⟨59103682123676967317046403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78804909498235956422728537 59103682123676967317046403)
                ·
                  refine ⟨88655523185515450975569605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59103682123676967317046403 88655523185515450975569605)
                  ·
                    refine ⟨16622910597284147057919301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88655523185515450975569605 16622910597284147057919301)
                    ·
                      refine ⟨3116795736990777573359869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16622910597284147057919301 3116795736990777573359869)
                      ·
                        rfl

theorem cell23_6069938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_6069938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069938 prefixEnd_6069938 := by exact prefixLift 6069938
  have htrace : WordTrace (prefixWord ++ tailWord_6069938) baseStart_6069938 baseEnd_6069938 := by
    simpa [prefixWord, tailWord_6069938, baseEnd_6069938] using wordTrace_append hprefix tailTrace_6069938
  have hstable : (prefixWord ++ tailWord_6069938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069938).length < 2 ^ (prefixWord ++ tailWord_6069938).sum := by decide
  have hdescent : baseEnd_6069938 < baseStart_6069938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6069988 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_6069988 : Nat := 118140960795 + 6069988 * 2 ^ 59
def prefixEnd_6069988 : Nat := 4983230072969 + 3 ^ 40 * 6069988 * 2
def baseEnd_6069988 : Nat := 3116821411023502377734639

theorem tailTrace_6069988 : CollatzResearch.WordTrace tailWord_6069988 prefixEnd_6069988 3116821411023502377734639 := by
  unfold tailWord_6069988
  simp only [CollatzResearch.WordTrace]
  refine ⟨110695325166738811130941309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147593766888985081507921745 110695325166738811130941309)
  ·
    refine ⟨41510746937527054174102991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110695325166738811130941309 41510746937527054174102991)
    ·
      refine ⟨62266120406290581261154487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41510746937527054174102991 62266120406290581261154487)
      ·
        refine ⟨93399180609435871891731731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62266120406290581261154487 93399180609435871891731731)
        ·
          refine ⟨140098770914153807837597597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93399180609435871891731731 140098770914153807837597597)
          ·
            refine ⟨52537039092807677939099099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140098770914153807837597597 52537039092807677939099099)
            ·
              refine ⟨78805558639211516908648649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52537039092807677939099099 78805558639211516908648649)
              ·
                refine ⟨59104168979408637681486487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78805558639211516908648649 59104168979408637681486487)
                ·
                  refine ⟨88656253469112956522229731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59104168979408637681486487 88656253469112956522229731)
                  ·
                    refine ⟨132984380203669434783344597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88656253469112956522229731 132984380203669434783344597)
                    ·
                      refine ⟨3116821411023502377734639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132984380203669434783344597 3116821411023502377734639)
                      ·
                        rfl

theorem cell23_6069988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_6069988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6069988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6069988 prefixEnd_6069988 := by exact prefixLift 6069988
  have htrace : WordTrace (prefixWord ++ tailWord_6069988) baseStart_6069988 baseEnd_6069988 := by
    simpa [prefixWord, tailWord_6069988, baseEnd_6069988] using wordTrace_append hprefix tailTrace_6069988
  have hstable : (prefixWord ++ tailWord_6069988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6069988).length < 2 ^ (prefixWord ++ tailWord_6069988).sum := by decide
  have hdescent : baseEnd_6069988 < baseStart_6069988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6069988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070015 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_6070015 : Nat := 118140960795 + 6070015 * 2 ^ 59
def prefixEnd_6070015 : Nat := 4983230072969 + 3 ^ 40 * 6070015 * 2
def baseEnd_6070015 : Nat := 3116835275001173772097015

theorem tailTrace_6070015 : CollatzResearch.WordTrace tailWord_6070015 prefixEnd_6070015 3116835275001173772097015 := by
  unfold tailWord_6070015
  simp only [CollatzResearch.WordTrace]
  refine ⟨221391635104379805873115499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147594423402919870582076999 221391635104379805873115499)
  ·
    refine ⟨332087452656569708809673249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221391635104379805873115499 332087452656569708809673249)
    ·
      refine ⟨249065589492427281607254937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332087452656569708809673249 249065589492427281607254937)
      ·
        refine ⟨186799192119320461205441203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249065589492427281607254937 186799192119320461205441203)
        ·
          refine ⟨280198788178980691808161805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186799192119320461205441203 280198788178980691808161805)
          ·
            refine ⟨105074545567117759428060677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280198788178980691808161805 105074545567117759428060677)
            ·
              refine ⟨19701477293834579892761377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105074545567117759428060677 19701477293834579892761377)
              ·
                refine ⟨14776107970375934919571033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19701477293834579892761377 14776107970375934919571033)
                ·
                  refine ⟨11082080977781951189678275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14776107970375934919571033 11082080977781951189678275)
                  ·
                    refine ⟨16623121466672926784517413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11082080977781951189678275 16623121466672926784517413)
                    ·
                      refine ⟨3116835275001173772097015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16623121466672926784517413 3116835275001173772097015)
                      ·
                        rfl

theorem cell23_6070015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_6070015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070015 prefixEnd_6070015 := by exact prefixLift 6070015
  have htrace : WordTrace (prefixWord ++ tailWord_6070015) baseStart_6070015 baseEnd_6070015 := by
    simpa [prefixWord, tailWord_6070015, baseEnd_6070015] using wordTrace_append hprefix tailTrace_6070015
  have hstable : (prefixWord ++ tailWord_6070015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070015).length < 2 ^ (prefixWord ++ tailWord_6070015).sum := by decide
  have hdescent : baseEnd_6070015 < baseStart_6070015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070025 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 3, 4]
def baseStart_6070025 : Nat := 118140960795 + 6070025 * 2 ^ 59
def prefixEnd_6070025 : Nat := 4983230072969 + 3 ^ 40 * 6070025 * 2
def baseEnd_6070025 : Nat := 1038946803269239577657323

theorem tailTrace_6070025 : CollatzResearch.WordTrace tailWord_6070025 prefixEnd_6070025 1038946803269239577657323 := by
  unfold tailWord_6070025
  simp only [CollatzResearch.WordTrace]
  refine ⟨221391999834343577580979529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147594666556229051720653019 221391999834343577580979529)
  ·
    refine ⟨166043999875757683185734647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221391999834343577580979529 166043999875757683185734647)
    ·
      refine ⟨249065999813636524778601971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166043999875757683185734647 249065999813636524778601971)
      ·
        refine ⟨373598999720454787167902957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249065999813636524778601971 373598999720454787167902957)
        ·
          refine ⟨140099624895170545187963609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373598999720454787167902957 140099624895170545187963609)
          ·
            refine ⟨105074718671377908890972707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140099624895170545187963609 105074718671377908890972707)
            ·
              refine ⟨157612078007066863336459061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105074718671377908890972707 157612078007066863336459061)
              ·
                refine ⟨14776132313162518437793037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157612078007066863336459061 14776132313162518437793037)
                ·
                  refine ⟨5541049617435944414172389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14776132313162518437793037 5541049617435944414172389)
                  ·
                    refine ⟨1038946803269239577657323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541049617435944414172389 1038946803269239577657323)
                    ·
                      rfl

theorem cell23_6070025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_6070025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070025 prefixEnd_6070025 := by exact prefixLift 6070025
  have htrace : WordTrace (prefixWord ++ tailWord_6070025) baseStart_6070025 baseEnd_6070025 := by
    simpa [prefixWord, tailWord_6070025, baseEnd_6070025] using wordTrace_append hprefix tailTrace_6070025
  have hstable : (prefixWord ++ tailWord_6070025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070025).length < 2 ^ (prefixWord ++ tailWord_6070025).sum := by decide
  have hdescent : baseEnd_6070025 < baseStart_6070025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070042 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_6070042 : Nat := 118140960795 + 6070042 * 2 ^ 59
def prefixEnd_6070042 : Nat := 4983230072969 + 3 ^ 40 * 6070042 * 2
def baseEnd_6070042 : Nat := 1038949712992948388819797

theorem tailTrace_6070042 : CollatzResearch.WordTrace tailWord_6070042 prefixEnd_6070042 1038949712992948388819797 := by
  unfold tailWord_6070042
  simp only [CollatzResearch.WordTrace]
  refine ⟨55348154968820497371087095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147595079916854659656232253 55348154968820497371087095)
  ·
    refine ⟨83022232453230746056630643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55348154968820497371087095 83022232453230746056630643)
    ·
      refine ⟨124533348679846119084945965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83022232453230746056630643 124533348679846119084945965)
      ·
        refine ⟨46700005754942294656854737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124533348679846119084945965 46700005754942294656854737)
        ·
          refine ⟨35025004316206720992641053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46700005754942294656854737 35025004316206720992641053)
          ·
            refine ⟨13134376618577520372240395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35025004316206720992641053 13134376618577520372240395)
            ·
              refine ⟨19701564927866280558360593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134376618577520372240395 19701564927866280558360593)
              ·
                refine ⟨14776173695899710418770445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19701564927866280558360593 14776173695899710418770445)
                ·
                  refine ⟨5541065135962391407038917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14776173695899710418770445 5541065135962391407038917)
                  ·
                    refine ⟨1038949712992948388819797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541065135962391407038917 1038949712992948388819797)
                    ·
                      rfl

theorem cell23_6070042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_6070042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070042 prefixEnd_6070042 := by exact prefixLift 6070042
  have htrace : WordTrace (prefixWord ++ tailWord_6070042) baseStart_6070042 baseEnd_6070042 := by
    simpa [prefixWord, tailWord_6070042, baseEnd_6070042] using wordTrace_append hprefix tailTrace_6070042
  have hstable : (prefixWord ++ tailWord_6070042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070042).length < 2 ^ (prefixWord ++ tailWord_6070042).sum := by decide
  have hdescent : baseEnd_6070042 < baseStart_6070042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070052 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_6070052 : Nat := 118140960795 + 6070052 * 2 ^ 59
def prefixEnd_6070052 : Nat := 4983230072969 + 3 ^ 40 * 6070052 * 2
def baseEnd_6070052 : Nat := 3116854273785390127334345

theorem tailTrace_6070052 : CollatzResearch.WordTrace tailWord_6070052 prefixEnd_6070052 3116854273785390127334345 := by
  unfold tailWord_6070052
  simp only [CollatzResearch.WordTrace]
  refine ⟨110696492302622880596106205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147595323070163840794808273 110696492302622880596106205)
  ·
    refine ⟨41511184613483580223539827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110696492302622880596106205 41511184613483580223539827)
    ·
      refine ⟨62266776920225370335309741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41511184613483580223539827 62266776920225370335309741)
      ·
        refine ⟨23350041345084513875741153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62266776920225370335309741 23350041345084513875741153)
        ·
          refine ⟨17512531008813385406805865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23350041345084513875741153 17512531008813385406805865)
          ·
            refine ⟨13134398256610039055104399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17512531008813385406805865 13134398256610039055104399)
            ·
              refine ⟨19701597384915058582656599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134398256610039055104399 19701597384915058582656599)
              ·
                refine ⟨29552396077372587873984899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19701597384915058582656599 29552396077372587873984899)
                ·
                  refine ⟨44328594116058881810977349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29552396077372587873984899 44328594116058881810977349)
                  ·
                    refine ⟨8311611396761040339558253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44328594116058881810977349 8311611396761040339558253)
                    ·
                      refine ⟨3116854273785390127334345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8311611396761040339558253 3116854273785390127334345)
                      ·
                        rfl

theorem cell23_6070052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_6070052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070052 prefixEnd_6070052 := by exact prefixLift 6070052
  have htrace : WordTrace (prefixWord ++ tailWord_6070052) baseStart_6070052 baseEnd_6070052 := by
    simpa [prefixWord, tailWord_6070052, baseEnd_6070052] using wordTrace_append hprefix tailTrace_6070052
  have hstable : (prefixWord ++ tailWord_6070052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070052).length < 2 ^ (prefixWord ++ tailWord_6070052).sum := by decide
  have hdescent : baseEnd_6070052 < baseStart_6070052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070072 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 6]
def baseStart_6070072 : Nat := 118140960795 + 6070072 * 2 ^ 59
def prefixEnd_6070072 : Nat := 4983230072969 + 3 ^ 40 * 6070072 * 2
def baseEnd_6070072 : Nat := 346318282599831116564917

theorem tailTrace_6070072 : CollatzResearch.WordTrace tailWord_6070072 prefixEnd_6070072 346318282599831116564917 := by
  unfold tailWord_6070072
  simp only [CollatzResearch.WordTrace]
  refine ⟨110696857032586652303970235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147595809376782203071960313 110696857032586652303970235)
  ·
    refine ⟨166045285548879978455955353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110696857032586652303970235 166045285548879978455955353)
    ·
      refine ⟨124533964161659983841966515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166045285548879978455955353 124533964161659983841966515)
      ·
        refine ⟨186800946242489975762949773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124533964161659983841966515 186800946242489975762949773)
        ·
          refine ⟨70050354840933740911106165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186800946242489975762949773 70050354840933740911106165)
          ·
            refine ⟨6567220766337538210416203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70050354840933740911106165 6567220766337538210416203)
            ·
              refine ⟨9850831149506307315624305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6567220766337538210416203 9850831149506307315624305)
              ·
                refine ⟨7388123362129730486718229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9850831149506307315624305 7388123362129730486718229)
                ·
                  refine ⟨346318282599831116564917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7388123362129730486718229 346318282599831116564917)
                  ·
                    rfl

theorem cell23_6070072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 6].length) (baseStart_6070072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070072 prefixEnd_6070072 := by exact prefixLift 6070072
  have htrace : WordTrace (prefixWord ++ tailWord_6070072) baseStart_6070072 baseEnd_6070072 := by
    simpa [prefixWord, tailWord_6070072, baseEnd_6070072] using wordTrace_append hprefix tailTrace_6070072
  have hstable : (prefixWord ++ tailWord_6070072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070072).length < 2 ^ (prefixWord ++ tailWord_6070072).sum := by decide
  have hdescent : baseEnd_6070072 < baseStart_6070072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070126 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_6070126 : Nat := 118140960795 + 6070126 * 2 ^ 59
def prefixEnd_6070126 : Nat := 4983230072969 + 3 ^ 40 * 6070126 * 2
def baseEnd_6070126 : Nat := 3116892271353822837809005

theorem tailTrace_6070126 : CollatzResearch.WordTrace tailWord_6070126 prefixEnd_6070126 3116892271353822837809005 := by
  unfold tailWord_6070126
  simp only [CollatzResearch.WordTrace]
  refine ⟨27674460450872208978800779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147597122404651781220270821 27674460450872208978800779)
  ·
    refine ⟨41511690676308313468201169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27674460450872208978800779 41511690676308313468201169)
    ·
      refine ⟨31133768007231235101150877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41511690676308313468201169 31133768007231235101150877)
      ·
        refine ⟨11675163002711713162931579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31133768007231235101150877 11675163002711713162931579)
        ·
          refine ⟨17512744504067569744397369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11675163002711713162931579 17512744504067569744397369)
          ·
            refine ⟨13134558378050677308298027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17512744504067569744397369 13134558378050677308298027)
            ·
              refine ⟨19701837567076015962447041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134558378050677308298027 19701837567076015962447041)
              ·
                refine ⟨14776378175307011971835281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19701837567076015962447041 14776378175307011971835281)
                ·
                  refine ⟨11082283631480258978876461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14776378175307011971835281 11082283631480258978876461)
                  ·
                    refine ⟨4155856361805097117078673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11082283631480258978876461 4155856361805097117078673)
                    ·
                      refine ⟨3116892271353822837809005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4155856361805097117078673 3116892271353822837809005)
                      ·
                        rfl

theorem cell23_6070126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_6070126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070126 prefixEnd_6070126 := by exact prefixLift 6070126
  have htrace : WordTrace (prefixWord ++ tailWord_6070126) baseStart_6070126 baseEnd_6070126 := by
    simpa [prefixWord, tailWord_6070126, baseEnd_6070126] using wordTrace_append hprefix tailTrace_6070126
  have hstable : (prefixWord ++ tailWord_6070126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070126).length < 2 ^ (prefixWord ++ tailWord_6070126).sum := by decide
  have hdescent : baseEnd_6070126 < baseStart_6070126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070133 : List Nat := [1, 3, 4, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_6070133 : Nat := 118140960795 + 6070133 * 2 ^ 59
def prefixEnd_6070133 : Nat := 4983230072969 + 3 ^ 40 * 6070133 * 2
def baseEnd_6070133 : Nat := 3116895865718404310421473

theorem tailTrace_6070133 : CollatzResearch.WordTrace tailWord_6070133 prefixEnd_6070133 3116895865718404310421473 := by
  unfold tailWord_6070133
  simp only [CollatzResearch.WordTrace]
  refine ⟨221395938917952312025911053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147597292611968208017274035 221395938917952312025911053)
  ·
    refine ⟨83023477094232117009716645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221395938917952312025911053 83023477094232117009716645)
    ·
      refine ⟨15566901955168521939321871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83023477094232117009716645 15566901955168521939321871)
      ·
        refine ⟨23350352932752782908982807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15566901955168521939321871 23350352932752782908982807)
        ·
          refine ⟨35025529399129174363474211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23350352932752782908982807 35025529399129174363474211)
          ·
            refine ⟨52538294098693761545211317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35025529399129174363474211 52538294098693761545211317)
            ·
              refine ⟨4925465071752540144863561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52538294098693761545211317 4925465071752540144863561)
              ·
                refine ⟨3694098803814405108647671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925465071752540144863561 3694098803814405108647671)
                ·
                  refine ⟨5541148205721607662971507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694098803814405108647671 5541148205721607662971507)
                  ·
                    refine ⟨8311722308582411494457261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5541148205721607662971507 8311722308582411494457261)
                    ·
                      refine ⟨3116895865718404310421473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8311722308582411494457261 3116895865718404310421473)
                      ·
                        rfl

theorem cell23_6070133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_6070133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070133 prefixEnd_6070133 := by exact prefixLift 6070133
  have htrace : WordTrace (prefixWord ++ tailWord_6070133) baseStart_6070133 baseEnd_6070133 := by
    simpa [prefixWord, tailWord_6070133, baseEnd_6070133] using wordTrace_append hprefix tailTrace_6070133
  have hstable : (prefixWord ++ tailWord_6070133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070133).length < 2 ^ (prefixWord ++ tailWord_6070133).sum := by decide
  have hdescent : baseEnd_6070133 < baseStart_6070133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070162 : List Nat := [3, 2, 3, 2, 1, 1, 2, 9]
def baseStart_6070162 : Nat := 118140960795 + 6070162 * 2 ^ 59
def prefixEnd_6070162 : Nat := 4983230072969 + 3 ^ 40 * 6070162 * 2
def baseEnd_6070162 : Nat := 115441139135458692479957

theorem tailTrace_6070162 : CollatzResearch.WordTrace tailWord_6070162 prefixEnd_6070162 115441139135458692479957 := by
  unfold tailWord_6070162
  simp only [CollatzResearch.WordTrace]
  refine ⟨55349249158711812494679185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147597997756564833319144493 55349249158711812494679185)
  ·
    refine ⟨41511936869033859371009389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55349249158711812494679185 41511936869033859371009389)
    ·
      refine ⟨15566976325887697264128521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41511936869033859371009389 15566976325887697264128521)
      ·
        refine ⟨11675232244415772948096391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15566976325887697264128521 11675232244415772948096391)
        ·
          refine ⟨17512848366623659422144587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11675232244415772948096391 17512848366623659422144587)
          ·
            refine ⟨26269272549935489133216881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17512848366623659422144587 26269272549935489133216881)
            ·
              refine ⟨19701954412451616849912661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26269272549935489133216881 19701954412451616849912661)
              ·
                refine ⟨115441139135458692479957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19701954412451616849912661 115441139135458692479957)
                ·
                  rfl

theorem cell23_6070162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 9].length) (baseStart_6070162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070162 prefixEnd_6070162 := by exact prefixLift 6070162
  have htrace : WordTrace (prefixWord ++ tailWord_6070162) baseStart_6070162 baseEnd_6070162 := by
    simpa [prefixWord, tailWord_6070162, baseEnd_6070162] using wordTrace_append hprefix tailTrace_6070162
  have hstable : (prefixWord ++ tailWord_6070162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070162).length < 2 ^ (prefixWord ++ tailWord_6070162).sum := by decide
  have hdescent : baseEnd_6070162 < baseStart_6070162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070184 : List Nat := [2, 1, 6, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6070184 : Nat := 118140960795 + 6070184 * 2 ^ 59
def prefixEnd_6070184 : Nat := 4983230072969 + 3 ^ 40 * 6070184 * 2
def baseEnd_6070184 : Nat := 3116922053231783610883739

theorem tailTrace_6070184 : CollatzResearch.WordTrace tailWord_6070184 prefixEnd_6070184 3116922053231783610883739 := by
  unfold tailWord_6070184
  simp only [CollatzResearch.WordTrace]
  refine ⟨110698899520383773868008803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147598532693845031824011737 110698899520383773868008803)
  ·
    refine ⟨166048349280575660802013205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110698899520383773868008803 166048349280575660802013205)
    ·
      refine ⟨7783516372526984100094369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166048349280575660802013205 7783516372526984100094369)
      ·
        refine ⟨5837637279395238075070777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7783516372526984100094369 5837637279395238075070777)
        ·
          refine ⟨4378227959546428556303083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5837637279395238075070777 4378227959546428556303083)
          ·
            refine ⟨6567341939319642834454625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378227959546428556303083 6567341939319642834454625)
            ·
              refine ⟨4925506454489732125840969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6567341939319642834454625 4925506454489732125840969)
              ·
                refine ⟨3694129840867299094380727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925506454489732125840969 3694129840867299094380727)
                ·
                  refine ⟨5541194761300948641571091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694129840867299094380727 5541194761300948641571091)
                  ·
                    refine ⟨8311792141951422962356637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5541194761300948641571091 8311792141951422962356637)
                    ·
                      refine ⟨3116922053231783610883739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8311792141951422962356637 3116922053231783610883739)
                      ·
                        rfl

theorem cell23_6070184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6070184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070184 prefixEnd_6070184 := by exact prefixLift 6070184
  have htrace : WordTrace (prefixWord ++ tailWord_6070184) baseStart_6070184 baseEnd_6070184 := by
    simpa [prefixWord, tailWord_6070184, baseEnd_6070184] using wordTrace_append hprefix tailTrace_6070184
  have hstable : (prefixWord ++ tailWord_6070184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070184).length < 2 ^ (prefixWord ++ tailWord_6070184).sum := by decide
  have hdescent : baseEnd_6070184 < baseStart_6070184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070195 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4]
def baseStart_6070195 : Nat := 118140960795 + 6070195 * 2 ^ 59
def prefixEnd_6070195 : Nat := 4983230072969 + 3 ^ 40 * 6070195 * 2
def baseEnd_6070195 : Nat := 3116927701518983067846187

theorem tailTrace_6070195 : CollatzResearch.WordTrace tailWord_6070195 prefixEnd_6070195 3116927701518983067846187 := by
  unfold tailWord_6070195
  simp only [CollatzResearch.WordTrace]
  refine ⟨221398200243727696614668039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147598800162485131076445359 221398200243727696614668039)
  ·
    refine ⟨332097300365591544922002059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221398200243727696614668039 332097300365591544922002059)
    ·
      refine ⟨498145950548387317383003089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332097300365591544922002059 498145950548387317383003089)
      ·
        refine ⟨373609462911290488037252317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498145950548387317383003089 373609462911290488037252317)
        ·
          refine ⟨140103548591733933013969619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373609462911290488037252317 140103548591733933013969619)
          ·
            refine ⟨210155322887600899520954429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140103548591733933013969619 210155322887600899520954429)
            ·
              refine ⟨78808246082850337320357911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210155322887600899520954429 78808246082850337320357911)
              ·
                refine ⟨118212369124275505980536867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78808246082850337320357911 118212369124275505980536867)
                ·
                  refine ⟨177318553686413258970805301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118212369124275505980536867 177318553686413258970805301)
                  ·
                    refine ⟨16623614408101243028512997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177318553686413258970805301 16623614408101243028512997)
                    ·
                      refine ⟨3116927701518983067846187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16623614408101243028512997 3116927701518983067846187)
                      ·
                        rfl

theorem cell23_6070195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_6070195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070195 prefixEnd_6070195 := by exact prefixLift 6070195
  have htrace : WordTrace (prefixWord ++ tailWord_6070195) baseStart_6070195 baseEnd_6070195 := by
    simpa [prefixWord, tailWord_6070195, baseEnd_6070195] using wordTrace_append hprefix tailTrace_6070195
  have hstable : (prefixWord ++ tailWord_6070195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070195).length < 2 ^ (prefixWord ++ tailWord_6070195).sum := by decide
  have hdescent : baseEnd_6070195 < baseStart_6070195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070196 : List Nat := [2, 5, 2, 1, 2, 2, 1, 8]
def baseStart_6070196 : Nat := 118140960795 + 6070196 * 2 ^ 59
def prefixEnd_6070196 : Nat := 4983230072969 + 3 ^ 40 * 6070196 * 2
def baseEnd_6070196 : Nat := 115441785740727317182729

theorem tailTrace_6070196 : CollatzResearch.WordTrace tailWord_6070196 prefixEnd_6070196 115441785740727317182729 := by
  unfold tailWord_6070196
  simp only [CollatzResearch.WordTrace]
  refine ⟨110699118358362036892727221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147598824477816049190302961 110699118358362036892727221)
  ·
    refine ⟨10378042346096440958693177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110699118358362036892727221 10378042346096440958693177)
    ·
      refine ⟨7783531759572330719019883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10378042346096440958693177 7783531759572330719019883)
      ·
        refine ⟨11675297639358496078529825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7783531759572330719019883 11675297639358496078529825)
        ·
          refine ⟨8756473229518872058897369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11675297639358496078529825 8756473229518872058897369)
          ·
            refine ⟨6567354922139154044173027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8756473229518872058897369 6567354922139154044173027)
            ·
              refine ⟨9851032383208731066259541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6567354922139154044173027 9851032383208731066259541)
              ·
                refine ⟨115441785740727317182729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9851032383208731066259541 115441785740727317182729)
                ·
                  rfl

theorem cell23_6070196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 8].length) (baseStart_6070196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070196 prefixEnd_6070196 := by exact prefixLift 6070196
  have htrace : WordTrace (prefixWord ++ tailWord_6070196) baseStart_6070196 baseEnd_6070196 := by
    simpa [prefixWord, tailWord_6070196, baseEnd_6070196] using wordTrace_append hprefix tailTrace_6070196
  have hstable : (prefixWord ++ tailWord_6070196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070196).length < 2 ^ (prefixWord ++ tailWord_6070196).sum := by decide
  have hdescent : baseEnd_6070196 < baseStart_6070196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070206 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_6070206 : Nat := 118140960795 + 6070206 * 2 ^ 59
def prefixEnd_6070206 : Nat := 4983230072969 + 3 ^ 40 * 6070206 * 2
def baseEnd_6070206 : Nat := 3116933349806182524808637

theorem tailTrace_6070206 : CollatzResearch.WordTrace tailWord_6070206 prefixEnd_6070206 3116933349806182524808637 := by
  unfold tailWord_6070206
  simp only [CollatzResearch.WordTrace]
  refine ⟨27674825180835980686664809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147599067631125230328878981 27674825180835980686664809)
  ·
    refine ⟨20756118885626985514998607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27674825180835980686664809 20756118885626985514998607)
    ·
      refine ⟨31134178328440478272497911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20756118885626985514998607 31134178328440478272497911)
      ·
        refine ⟨46701267492660717408746867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31134178328440478272497911 46701267492660717408746867)
        ·
          refine ⟨70051901238991076113120301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46701267492660717408746867 70051901238991076113120301)
          ·
            refine ⟨26269462964621653542420113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70051901238991076113120301 26269462964621653542420113)
            ·
              refine ⟨19702097223466240156815085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26269462964621653542420113 19702097223466240156815085)
              ·
                refine ⟨7388286458799840058805657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19702097223466240156815085 7388286458799840058805657)
                ·
                  refine ⟨5541214844099880044104243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7388286458799840058805657 5541214844099880044104243)
                  ·
                    refine ⟨8311822266149820066156365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5541214844099880044104243 8311822266149820066156365)
                    ·
                      refine ⟨3116933349806182524808637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8311822266149820066156365 3116933349806182524808637)
                      ·
                        rfl

theorem cell23_6070206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_6070206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070206 prefixEnd_6070206 := by exact prefixLift 6070206
  have htrace : WordTrace (prefixWord ++ tailWord_6070206) baseStart_6070206 baseEnd_6070206 := by
    simpa [prefixWord, tailWord_6070206, baseEnd_6070206] using wordTrace_append hprefix tailTrace_6070206
  have hstable : (prefixWord ++ tailWord_6070206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070206).length < 2 ^ (prefixWord ++ tailWord_6070206).sum := by decide
  have hdescent : baseEnd_6070206 < baseStart_6070206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070346 : List Nat := [3, 1, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_6070346 : Nat := 118140960795 + 6070346 * 2 ^ 59
def prefixEnd_6070346 : Nat := 4983230072969 + 3 ^ 40 * 6070346 * 2
def baseEnd_6070346 : Nat := 1039001745699270659019331

theorem tailTrace_6070346 : CollatzResearch.WordTrace tailWord_6070346 prefixEnd_6070346 1039001745699270659019331 := by
  unfold tailWord_6070346
  simp only [CollatzResearch.WordTrace]
  refine ⟨55350926916545162350853723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147602471777453766268943261 55350926916545162350853723)
  ·
    refine ⟨83026390374817743526280585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55350926916545162350853723 83026390374817743526280585)
    ·
      refine ⟨62269792781113307644710439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83026390374817743526280585 62269792781113307644710439)
      ·
        refine ⟨93404689171669961467065659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62269792781113307644710439 93404689171669961467065659)
        ·
          refine ⟨140107033757504942200598489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93404689171669961467065659 140107033757504942200598489)
          ·
            refine ⟨105080275318128706650448867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140107033757504942200598489 105080275318128706650448867)
            ·
              refine ⟨157620412977193059975673301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105080275318128706650448867 157620412977193059975673301)
              ·
                refine ⟨3694228429152962343179843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 157620412977193059975673301 3694228429152962343179843)
                ·
                  refine ⟨5541342643729443514769765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694228429152962343179843 5541342643729443514769765)
                  ·
                    refine ⟨1039001745699270659019331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541342643729443514769765 1039001745699270659019331)
                    ·
                      rfl

theorem cell23_6070346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_6070346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070346 prefixEnd_6070346 := by exact prefixLift 6070346
  have htrace : WordTrace (prefixWord ++ tailWord_6070346) baseStart_6070346 baseEnd_6070346 := by
    simpa [prefixWord, tailWord_6070346, baseEnd_6070346] using wordTrace_append hprefix tailTrace_6070346
  have hstable : (prefixWord ++ tailWord_6070346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070346).length < 2 ^ (prefixWord ++ tailWord_6070346).sum := by decide
  have hdescent : baseEnd_6070346 < baseStart_6070346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070349 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6070349 : Nat := 118140960795 + 6070349 * 2 ^ 59
def prefixEnd_6070349 : Nat := 4983230072969 + 3 ^ 40 * 6070349 * 2
def baseEnd_6070349 : Nat := 3117006777539775465320479

theorem tailTrace_6070349 : CollatzResearch.WordTrace tailWord_6070349 prefixEnd_6070349 3117006777539775465320479 := by
  unfold tailWord_6070349
  simp only [CollatzResearch.WordTrace]
  refine ⟨221403817085169780915774101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147602544723446520610516067 221403817085169780915774101)
  ·
    refine ⟨10378303925867333480426911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 221403817085169780915774101 10378303925867333480426911)
    ·
      refine ⟨15567455888801000220640367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10378303925867333480426911 15567455888801000220640367)
      ·
        refine ⟨23351183833201500330960551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15567455888801000220640367 23351183833201500330960551)
        ·
          refine ⟨35026775749802250496440827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23351183833201500330960551 35026775749802250496440827)
          ·
            refine ⟨52540163624703375744661241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35026775749802250496440827 52540163624703375744661241)
            ·
              refine ⟨39405122718527531808495931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52540163624703375744661241 39405122718527531808495931)
              ·
                refine ⟨59107684077791297712743897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39405122718527531808495931 59107684077791297712743897)
                ·
                  refine ⟨44330763058343473284557923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59107684077791297712743897 44330763058343473284557923)
                  ·
                    refine ⟨66496144587515209926836885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44330763058343473284557923 66496144587515209926836885)
                    ·
                      refine ⟨3117006777539775465320479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66496144587515209926836885 3117006777539775465320479)
                      ·
                        rfl

theorem cell23_6070349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6070349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070349 prefixEnd_6070349 := by exact prefixLift 6070349
  have htrace : WordTrace (prefixWord ++ tailWord_6070349) baseStart_6070349 baseEnd_6070349 := by
    simpa [prefixWord, tailWord_6070349, baseEnd_6070349] using wordTrace_append hprefix tailTrace_6070349
  have hstable : (prefixWord ++ tailWord_6070349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070349).length < 2 ^ (prefixWord ++ tailWord_6070349).sum := by decide
  have hdescent : baseEnd_6070349 < baseStart_6070349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070362 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_6070362 : Nat := 118140960795 + 6070362 * 2 ^ 59
def prefixEnd_6070362 : Nat := 4983230072969 + 3 ^ 40 * 6070362 * 2
def baseEnd_6070362 : Nat := 3117013452788283914457919

theorem tailTrace_6070362 : CollatzResearch.WordTrace tailWord_6070362 prefixEnd_6070362 3117013452788283914457919 := by
  unfold tailWord_6070362
  simp only [CollatzResearch.WordTrace]
  refine ⟨55351072808530671033999335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147602860822748456090664893 55351072808530671033999335)
  ·
    refine ⟨83026609212796006550999003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55351072808530671033999335 83026609212796006550999003)
    ·
      refine ⟨124539913819194009826498505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83026609212796006550999003 124539913819194009826498505)
      ·
        refine ⟨93404935364395507369873879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124539913819194009826498505 93404935364395507369873879)
        ·
          refine ⟨140107403046593261054810819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93404935364395507369873879 140107403046593261054810819)
          ·
            refine ⟨210161104569889891582216229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140107403046593261054810819 210161104569889891582216229)
            ·
              refine ⟨39405207106854354671665543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210161104569889891582216229 39405207106854354671665543)
              ·
                refine ⟨59107810660281532007498315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39405207106854354671665543 59107810660281532007498315)
                ·
                  refine ⟨88661715990422298011247473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59107810660281532007498315 88661715990422298011247473)
                  ·
                    refine ⟨66496286992816723508435605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88661715990422298011247473 66496286992816723508435605)
                    ·
                      refine ⟨3117013452788283914457919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66496286992816723508435605 3117013452788283914457919)
                      ·
                        rfl

theorem cell23_6070362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_6070362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070362 prefixEnd_6070362 := by exact prefixLift 6070362
  have htrace : WordTrace (prefixWord ++ tailWord_6070362) baseStart_6070362 baseEnd_6070362 := by
    simpa [prefixWord, tailWord_6070362, baseEnd_6070362] using wordTrace_append hprefix tailTrace_6070362
  have hstable : (prefixWord ++ tailWord_6070362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070362).length < 2 ^ (prefixWord ++ tailWord_6070362).sum := by decide
  have hdescent : baseEnd_6070362 < baseStart_6070362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070386 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_6070386 : Nat := 118140960795 + 6070386 * 2 ^ 59
def prefixEnd_6070386 : Nat := 4983230072969 + 3 ^ 40 * 6070386 * 2
def baseEnd_6070386 : Nat := 3117025776323991820557809

theorem tailTrace_6070386 : CollatzResearch.WordTrace tailWord_6070386 prefixEnd_6070386 3117025776323991820557809 := by
  unfold tailWord_6070386
  simp only [CollatzResearch.WordTrace]
  refine ⟨55351291646508934058717753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147603444390690490823247341 55351291646508934058717753)
  ·
    refine ⟨41513468734881700544038315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55351291646508934058717753 41513468734881700544038315)
    ·
      refine ⟨62270203102322550816057473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41513468734881700544038315 62270203102322550816057473)
      ·
        refine ⟨46702652326741913112043105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62270203102322550816057473 46702652326741913112043105)
        ·
          refine ⟨35026989245056434834032329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46702652326741913112043105 35026989245056434834032329)
          ·
            refine ⟨26270241933792326125524247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35026989245056434834032329 26270241933792326125524247)
            ·
              refine ⟨39405362900688489188286371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26270241933792326125524247 39405362900688489188286371)
              ·
                refine ⟨59108044351032733782429557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39405362900688489188286371 59108044351032733782429557)
                ·
                  refine ⟨5541379157909318792102771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59108044351032733782429557 5541379157909318792102771)
                  ·
                    refine ⟨8312068736863978188154157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5541379157909318792102771 8312068736863978188154157)
                    ·
                      refine ⟨3117025776323991820557809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8312068736863978188154157 3117025776323991820557809)
                      ·
                        rfl

theorem cell23_6070386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_6070386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070386 prefixEnd_6070386 := by exact prefixLift 6070386
  have htrace : WordTrace (prefixWord ++ tailWord_6070386) baseStart_6070386 baseEnd_6070386 := by
    simpa [prefixWord, tailWord_6070386, baseEnd_6070386] using wordTrace_append hprefix tailTrace_6070386
  have hstable : (prefixWord ++ tailWord_6070386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070386).length < 2 ^ (prefixWord ++ tailWord_6070386).sum := by decide
  have hdescent : baseEnd_6070386 < baseStart_6070386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070396 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_6070396 : Nat := 118140960795 + 6070396 * 2 ^ 59
def prefixEnd_6070396 : Nat := 4983230072969 + 3 ^ 40 * 6070396 * 2
def baseEnd_6070396 : Nat := 3117030911130536781432763

theorem tailTrace_6070396 : CollatzResearch.WordTrace tailWord_6070396 prefixEnd_6070396 3117030911130536781432763 := by
  unfold tailWord_6070396
  simp only [CollatzResearch.WordTrace]
  refine ⟨110702765657999753971367521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147603687543999671961823361 110702765657999753971367521)
  ·
    refine ⟨83027074243499815478525641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110702765657999753971367521 83027074243499815478525641)
    ·
      refine ⟨62270305682624861608894231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83027074243499815478525641 62270305682624861608894231)
      ·
        refine ⟨93405458523937292413341347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62270305682624861608894231 93405458523937292413341347)
        ·
          refine ⟨140108187785905938620012021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93405458523937292413341347 140108187785905938620012021)
          ·
            refine ⟨13135142604928681745626127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140108187785905938620012021 13135142604928681745626127)
            ·
              refine ⟨19702713907393022618439191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13135142604928681745626127 19702713907393022618439191)
              ·
                refine ⟨29554070861089533927658787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19702713907393022618439191 29554070861089533927658787)
                ·
                  refine ⟨44331106291634300891488181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29554070861089533927658787 44331106291634300891488181)
                  ·
                    refine ⟨4156041214840715708577017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44331106291634300891488181 4156041214840715708577017)
                    ·
                      refine ⟨3117030911130536781432763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156041214840715708577017 3117030911130536781432763)
                      ·
                        rfl

theorem cell23_6070396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_6070396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070396 prefixEnd_6070396 := by exact prefixLift 6070396
  have htrace : WordTrace (prefixWord ++ tailWord_6070396) baseStart_6070396 baseEnd_6070396 := by
    simpa [prefixWord, tailWord_6070396, baseEnd_6070396] using wordTrace_append hprefix tailTrace_6070396
  have hstable : (prefixWord ++ tailWord_6070396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070396).length < 2 ^ (prefixWord ++ tailWord_6070396).sum := by decide
  have hdescent : baseEnd_6070396 < baseStart_6070396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070403 : List Nat := [1, 1, 1, 3, 3, 3, 1, 5, 1, 1, 3]
def baseStart_6070403 : Nat := 118140960795 + 6070403 * 2 ^ 59
def prefixEnd_6070403 : Nat := 4983230072969 + 3 ^ 40 * 6070403 * 2
def baseEnd_6070403 : Nat := 3117034505495118254045231

theorem tailTrace_6070403 : CollatzResearch.WordTrace tailWord_6070403 prefixEnd_6070403 3117034505495118254045231 := by
  unfold tailWord_6070403
  simp only [CollatzResearch.WordTrace]
  refine ⟨221405786626974148138239863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147603857751316098758826575 221405786626974148138239863)
  ·
    refine ⟨332108679940461222207359795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221405786626974148138239863 332108679940461222207359795)
    ·
      refine ⟨498163019910691833311039693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332108679940461222207359795 498163019910691833311039693)
      ·
        refine ⟨186811132466509437491639885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498163019910691833311039693 186811132466509437491639885)
        ·
          refine ⟨70054174674941039059364957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186811132466509437491639885 70054174674941039059364957)
          ·
            refine ⟨26270315503102889647261859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70054174674941039059364957 26270315503102889647261859)
            ·
              refine ⟨39405473254654334470892789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26270315503102889647261859 39405473254654334470892789)
              ·
                refine ⟨3694263117623843856646199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39405473254654334470892789 3694263117623843856646199)
                ·
                  refine ⟨5541394676435765784969299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694263117623843856646199 5541394676435765784969299)
                  ·
                    refine ⟨8312092014653648677453949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5541394676435765784969299 8312092014653648677453949)
                    ·
                      refine ⟨3117034505495118254045231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8312092014653648677453949 3117034505495118254045231)
                      ·
                        rfl

theorem cell23_6070403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_6070403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070403 prefixEnd_6070403 := by exact prefixLift 6070403
  have htrace : WordTrace (prefixWord ++ tailWord_6070403) baseStart_6070403 baseEnd_6070403 := by
    simpa [prefixWord, tailWord_6070403, baseEnd_6070403] using wordTrace_append hprefix tailTrace_6070403
  have hstable : (prefixWord ++ tailWord_6070403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070403).length < 2 ^ (prefixWord ++ tailWord_6070403).sum := by decide
  have hdescent : baseEnd_6070403 < baseStart_6070403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070429 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_6070429 : Nat := 118140960795 + 6070429 * 2 ^ 59
def prefixEnd_6070429 : Nat := 4983230072969 + 3 ^ 40 * 6070429 * 2
def baseEnd_6070429 : Nat := 3117047855992135152320111

theorem tailTrace_6070429 : CollatzResearch.WordTrace tailWord_6070429 prefixEnd_6070429 3117047855992135152320111 := by
  unfold tailWord_6070429
  simp only [CollatzResearch.WordTrace]
  refine ⟨221406734924879954578686341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147604489949919969719124227 221406734924879954578686341)
  ·
    refine ⟨41513762798414991483503689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221406734924879954578686341 41513762798414991483503689)
    ·
      refine ⟨31135322098811243612627767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41513762798414991483503689 31135322098811243612627767)
      ·
        refine ⟨46702983148216865418941651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31135322098811243612627767 46702983148216865418941651)
        ·
          refine ⟨70054474722325298128412477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46702983148216865418941651 70054474722325298128412477)
          ·
            refine ⟨26270428020871986798154679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70054474722325298128412477 26270428020871986798154679)
            ·
              refine ⟨39405642031307980197232019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26270428020871986798154679 39405642031307980197232019)
              ·
                refine ⟨59108463046961970295848029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39405642031307980197232019 59108463046961970295848029)
                ·
                  refine ⟨22165673642610738860943011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59108463046961970295848029 22165673642610738860943011)
                  ·
                    refine ⟨33248510463916108291414517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22165673642610738860943011 33248510463916108291414517)
                    ·
                      refine ⟨3117047855992135152320111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33248510463916108291414517 3117047855992135152320111)
                      ·
                        rfl

theorem cell23_6070429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_6070429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070429 prefixEnd_6070429 := by exact prefixLift 6070429
  have htrace : WordTrace (prefixWord ++ tailWord_6070429) baseStart_6070429 baseEnd_6070429 := by
    simpa [prefixWord, tailWord_6070429, baseEnd_6070429] using wordTrace_append hprefix tailTrace_6070429
  have hstable : (prefixWord ++ tailWord_6070429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070429).length < 2 ^ (prefixWord ++ tailWord_6070429).sum := by decide
  have hdescent : baseEnd_6070429 < baseStart_6070429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070459 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 3]
def baseStart_6070459 : Nat := 118140960795 + 6070459 * 2 ^ 59
def prefixEnd_6070459 : Nat := 4983230072969 + 3 ^ 40 * 6070459 * 2
def baseEnd_6070459 : Nat := 3117063260411770034944973

theorem tailTrace_6070459 : CollatzResearch.WordTrace tailWord_6070459 prefixEnd_6070459 3117063260411770034944973 := by
  unfold tailWord_6070459
  simp only [CollatzResearch.WordTrace]
  refine ⟨221407829114771269702278431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147605219409847513134852287 221407829114771269702278431)
  ·
    refine ⟨332111743672156904553417647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221407829114771269702278431 332111743672156904553417647)
    ·
      refine ⟨498167615508235356830126471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332111743672156904553417647 498167615508235356830126471)
      ·
        refine ⟨747251423262353035245189707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498167615508235356830126471 747251423262353035245189707)
        ·
          refine ⟨1120877134893529552867784561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747251423262353035245189707 1120877134893529552867784561)
          ·
            refine ⟨840657851170147164650838421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120877134893529552867784561 840657851170147164650838421)
            ·
              refine ⟨39405836773600648343008051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 840657851170147164650838421 39405836773600648343008051)
              ·
                refine ⟨59108755160400972514512077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39405836773600648343008051 59108755160400972514512077)
                ·
                  refine ⟨22165783185150364692942029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59108755160400972514512077 22165783185150364692942029)
                  ·
                    refine ⟨8312168694431386759853261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22165783185150364692942029 8312168694431386759853261)
                    ·
                      refine ⟨3117063260411770034944973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8312168694431386759853261 3117063260411770034944973)
                      ·
                        rfl

theorem cell23_6070459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 3].length) (baseStart_6070459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070459 prefixEnd_6070459 := by exact prefixLift 6070459
  have htrace : WordTrace (prefixWord ++ tailWord_6070459) baseStart_6070459 baseEnd_6070459 := by
    simpa [prefixWord, tailWord_6070459, baseEnd_6070459] using wordTrace_append hprefix tailTrace_6070459
  have hstable : (prefixWord ++ tailWord_6070459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070459).length < 2 ^ (prefixWord ++ tailWord_6070459).sum := by decide
  have hdescent : baseEnd_6070459 < baseStart_6070459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070519 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_6070519 : Nat := 118140960795 + 6070519 * 2 ^ 59
def prefixEnd_6070519 : Nat := 4983230072969 + 3 ^ 40 * 6070519 * 2
def baseEnd_6070519 : Nat := 3117094069251039800194697

theorem tailTrace_6070519 : CollatzResearch.WordTrace tailWord_6070519 prefixEnd_6070519 3117094069251039800194697 := by
  unfold tailWord_6070519
  simp only [CollatzResearch.WordTrace]
  refine ⟨221410017494553899949462611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147606678329702599966308407 221410017494553899949462611)
  ·
    refine ⟨332115026241830849924193917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221410017494553899949462611 332115026241830849924193917)
    ·
      refine ⟨124543134840686568721572719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332115026241830849924193917 124543134840686568721572719)
      ·
        refine ⟨186814702261029853082359079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124543134840686568721572719 186814702261029853082359079)
        ·
          refine ⟨280222053391544779623538619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186814702261029853082359079 280222053391544779623538619)
          ·
            refine ⟨420333080087317169435307929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280222053391544779623538619 420333080087317169435307929)
            ·
              refine ⟨315249810065487877076480947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420333080087317169435307929 315249810065487877076480947)
              ·
                refine ⟨472874715098231815614721421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315249810065487877076480947 472874715098231815614721421)
                ·
                  refine ⟨177328018161836930855520533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472874715098231815614721421 177328018161836930855520533)
                  ·
                    refine ⟨8312250851336106133852525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 177328018161836930855520533 8312250851336106133852525)
                    ·
                      refine ⟨3117094069251039800194697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8312250851336106133852525 3117094069251039800194697)
                      ·
                        rfl

theorem cell23_6070519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_6070519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070519 prefixEnd_6070519 := by exact prefixLift 6070519
  have htrace : WordTrace (prefixWord ++ tailWord_6070519) baseStart_6070519 baseEnd_6070519 := by
    simpa [prefixWord, tailWord_6070519, baseEnd_6070519] using wordTrace_append hprefix tailTrace_6070519
  have hstable : (prefixWord ++ tailWord_6070519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070519).length < 2 ^ (prefixWord ++ tailWord_6070519).sum := by decide
  have hdescent : baseEnd_6070519 < baseStart_6070519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070526 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6070526 : Nat := 118140960795 + 6070526 * 2 ^ 59
def prefixEnd_6070526 : Nat := 4983230072969 + 3 ^ 40 * 6070526 * 2
def baseEnd_6070526 : Nat := 1039032554538540424269055

theorem tailTrace_6070526 : CollatzResearch.WordTrace tailWord_6070526 prefixEnd_6070526 1039032554538540424269055 := by
  unfold tailWord_6070526
  simp only [CollatzResearch.WordTrace]
  refine ⟨27676284100691067518120929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147606848537019026763311621 27676284100691067518120929)
  ·
    refine ⟨20757213075518300638590697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27676284100691067518120929 20757213075518300638590697)
    ·
      refine ⟨15567909806638725478943023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20757213075518300638590697 15567909806638725478943023)
      ·
        refine ⟨23351864709958088218414535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15567909806638725478943023 23351864709958088218414535)
        ·
          refine ⟨35027797064937132327621803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23351864709958088218414535 35027797064937132327621803)
          ·
            refine ⟨52541695597405698491432705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35027797064937132327621803 52541695597405698491432705)
            ·
              refine ⟨39406271698054273868574529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52541695597405698491432705 39406271698054273868574529)
              ·
                refine ⟨29554703773540705401430897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39406271698054273868574529 29554703773540705401430897)
                ·
                  refine ⟨22166027830155529051073173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29554703773540705401430897 22166027830155529051073173)
                  ·
                    refine ⟨1039032554538540424269055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22166027830155529051073173 1039032554538540424269055)
                    ·
                      rfl

theorem cell23_6070526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6070526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070526 prefixEnd_6070526 := by exact prefixLift 6070526
  have htrace : WordTrace (prefixWord ++ tailWord_6070526) baseStart_6070526 baseEnd_6070526 := by
    simpa [prefixWord, tailWord_6070526, baseEnd_6070526] using wordTrace_append hprefix tailTrace_6070526
  have hstable : (prefixWord ++ tailWord_6070526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070526).length < 2 ^ (prefixWord ++ tailWord_6070526).sum := by decide
  have hdescent : baseEnd_6070526 < baseStart_6070526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070536 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_6070536 : Nat := 118140960795 + 6070536 * 2 ^ 59
def prefixEnd_6070536 : Nat := 4983230072969 + 3 ^ 40 * 6070536 * 2
def baseEnd_6070536 : Nat := 3117102798422166233682119

theorem tailTrace_6070536 : CollatzResearch.WordTrace tailWord_6070536 prefixEnd_6070536 3117102798422166233682119 := by
  unfold tailWord_6070536
  simp only [CollatzResearch.WordTrace]
  refine ⟨110705318767746155926415731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147607091690328207901887641 110705318767746155926415731)
  ·
    refine ⟨166057978151619233889623597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110705318767746155926415731 166057978151619233889623597)
    ·
      refine ⟨62271741806857212708608849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166057978151619233889623597 62271741806857212708608849)
      ·
        refine ⟨46703806355142909531456637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62271741806857212708608849 46703806355142909531456637)
        ·
          refine ⟨17513927383178591074296239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46703806355142909531456637 17513927383178591074296239)
          ·
            refine ⟨26270891074767886611444359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17513927383178591074296239 26270891074767886611444359)
            ·
              refine ⟨39406336612151829917166539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26270891074767886611444359 39406336612151829917166539)
              ·
                refine ⟨59109504918227744875749809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39406336612151829917166539 59109504918227744875749809)
                ·
                  refine ⟨44332128688670808656812357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59109504918227744875749809 44332128688670808656812357)
                  ·
                    refine ⟨8312274129125776623152317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44332128688670808656812357 8312274129125776623152317)
                    ·
                      refine ⟨3117102798422166233682119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8312274129125776623152317 3117102798422166233682119)
                      ·
                        rfl

theorem cell23_6070536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_6070536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070536 prefixEnd_6070536 := by exact prefixLift 6070536
  have htrace : WordTrace (prefixWord ++ tailWord_6070536) baseStart_6070536 baseEnd_6070536 := by
    simpa [prefixWord, tailWord_6070536, baseEnd_6070536] using wordTrace_append hprefix tailTrace_6070536
  have hstable : (prefixWord ++ tailWord_6070536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070536).length < 2 ^ (prefixWord ++ tailWord_6070536).sum := by decide
  have hdescent : baseEnd_6070536 < baseStart_6070536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070539 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 7]
def baseStart_6070539 : Nat := 118140960795 + 6070539 * 2 ^ 59
def prefixEnd_6070539 : Nat := 4983230072969 + 3 ^ 40 * 6070539 * 2
def baseEnd_6070539 : Nat := 346344926540458857993845

theorem tailTrace_6070539 : CollatzResearch.WordTrace tailWord_6070539 prefixEnd_6070539 346344926540458857993845 := by
  unfold tailWord_6070539
  simp only [CollatzResearch.WordTrace]
  refine ⟨221410746954481443365190671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147607164636320962243460447 221410746954481443365190671)
  ·
    refine ⟨332116120431722165047786007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221410746954481443365190671 332116120431722165047786007)
    ·
      refine ⟨498174180647583247571679011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332116120431722165047786007 498174180647583247571679011)
      ·
        refine ⟨747261270971374871357518517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498174180647583247571679011 747261270971374871357518517)
        ·
          refine ⟨70055744153566394189767361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 747261270971374871357518517 70055744153566394189767361)
          ·
            refine ⟨52541808115174795642325521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70055744153566394189767361 52541808115174795642325521)
            ·
              refine ⟨39406356086381096731744141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52541808115174795642325521 39406356086381096731744141)
              ·
                refine ⟨14777383532392911274404053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39406356086381096731744141 14777383532392911274404053)
                ·
                  refine ⟨346344926540458857993845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14777383532392911274404053 346344926540458857993845)
                  ·
                    rfl

theorem cell23_6070539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 7].length) (baseStart_6070539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070539 prefixEnd_6070539 := by exact prefixLift 6070539
  have htrace : WordTrace (prefixWord ++ tailWord_6070539) baseStart_6070539 baseEnd_6070539 := by
    simpa [prefixWord, tailWord_6070539, baseEnd_6070539] using wordTrace_append hprefix tailTrace_6070539
  have hstable : (prefixWord ++ tailWord_6070539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070539).length < 2 ^ (prefixWord ++ tailWord_6070539).sum := by decide
  have hdescent : baseEnd_6070539 < baseStart_6070539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070576 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 7, 2]
def baseStart_6070576 : Nat := 118140960795 + 6070576 * 2 ^ 59
def prefixEnd_6070576 : Nat := 4983230072969 + 3 ^ 40 * 6070576 * 2
def baseEnd_6070576 : Nat := 3117123337648346077181935

theorem tailTrace_6070576 : CollatzResearch.WordTrace tailWord_6070576 prefixEnd_6070576 3117123337648346077181935 := by
  unfold tailWord_6070576
  simp only [CollatzResearch.WordTrace]
  refine ⟨110706048227673699342143791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147608064303564932456191721 110706048227673699342143791)
  ·
    refine ⟨166059072341510549013215687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110706048227673699342143791 166059072341510549013215687)
    ·
      refine ⟨249088608512265823519823531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166059072341510549013215687 249088608512265823519823531)
      ·
        refine ⟨373632912768398735279735297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249088608512265823519823531 373632912768398735279735297)
        ·
          refine ⟨280224684576299051459801473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373632912768398735279735297 280224684576299051459801473)
          ·
            refine ⟨210168513432224288594851105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280224684576299051459801473 210168513432224288594851105)
            ·
              refine ⟨157626385074168216446138329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210168513432224288594851105 157626385074168216446138329)
              ·
                refine ⟨118219788805626162334603747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157626385074168216446138329 118219788805626162334603747)
                ·
                  refine ⟨177329683208439243501905621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118219788805626162334603747 177329683208439243501905621)
                  ·
                    refine ⟨4156164450197794769575913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 177329683208439243501905621 4156164450197794769575913)
                    ·
                      refine ⟨3117123337648346077181935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156164450197794769575913 3117123337648346077181935)
                      ·
                        rfl

theorem cell23_6070576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 7, 2].length) (baseStart_6070576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070576 prefixEnd_6070576 := by exact prefixLift 6070576
  have htrace : WordTrace (prefixWord ++ tailWord_6070576) baseStart_6070576 baseEnd_6070576 := by
    simpa [prefixWord, tailWord_6070576, baseEnd_6070576] using wordTrace_append hprefix tailTrace_6070576
  have hstable : (prefixWord ++ tailWord_6070576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070576).length < 2 ^ (prefixWord ++ tailWord_6070576).sum := by decide
  have hdescent : baseEnd_6070576 < baseStart_6070576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070606 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_6070606 : Nat := 118140960795 + 6070606 * 2 ^ 59
def prefixEnd_6070606 : Nat := 4983230072969 + 3 ^ 40 * 6070606 * 2
def baseEnd_6070606 : Nat := 3117138742067980959806797

theorem tailTrace_6070606 : CollatzResearch.WordTrace tailWord_6070606 prefixEnd_6070606 3117138742067980959806797 := by
  unfold tailWord_6070606
  simp only [CollatzResearch.WordTrace]
  refine ⟨27676648830654839225984959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147608793763492475871919781 27676648830654839225984959)
  ·
    refine ⟨41514973245982258838977439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27676648830654839225984959 41514973245982258838977439)
    ·
      refine ⟨62272459868973388258466159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41514973245982258838977439 62272459868973388258466159)
      ·
        refine ⟨93408689803460082387699239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62272459868973388258466159 93408689803460082387699239)
        ·
          refine ⟨140113034705190123581548859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93408689803460082387699239 140113034705190123581548859)
          ·
            refine ⟨210169552057785185372323289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140113034705190123581548859 210169552057785185372323289)
            ·
              refine ⟨157627164043338889029242467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210169552057785185372323289 157627164043338889029242467)
              ·
                refine ⟨236440746065008333543863701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157627164043338889029242467 236440746065008333543863701)
                ·
                  refine ⟨11083159971797265634868611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236440746065008333543863701 11083159971797265634868611)
                  ·
                    refine ⟨16624739957695898452302917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11083159971797265634868611 16624739957695898452302917)
                    ·
                      refine ⟨3117138742067980959806797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16624739957695898452302917 3117138742067980959806797)
                      ·
                        rfl

theorem cell23_6070606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_6070606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070606 prefixEnd_6070606 := by exact prefixLift 6070606
  have htrace : WordTrace (prefixWord ++ tailWord_6070606) baseStart_6070606 baseEnd_6070606 := by
    simpa [prefixWord, tailWord_6070606, baseEnd_6070606] using wordTrace_append hprefix tailTrace_6070606
  have hstable : (prefixWord ++ tailWord_6070606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070606).length < 2 ^ (prefixWord ++ tailWord_6070606).sum := by decide
  have hdescent : baseEnd_6070606 < baseStart_6070606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070616 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 5, 4]
def baseStart_6070616 : Nat := 118140960795 + 6070616 * 2 ^ 59
def prefixEnd_6070616 : Nat := 4983230072969 + 3 ^ 40 * 6070616 * 2
def baseEnd_6070616 : Nat := 1039047958958175306893917

theorem tailTrace_6070616 : CollatzResearch.WordTrace tailWord_6070616 prefixEnd_6070616 1039047958958175306893917 := by
  unfold tailWord_6070616
  simp only [CollatzResearch.WordTrace]
  refine ⟨110706777687601242757871851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147609036916801657010495801 110706777687601242757871851)
  ·
    refine ⟨166060166531401864136807777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110706777687601242757871851 166060166531401864136807777)
    ·
      refine ⟨124545124898551398102605833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166060166531401864136807777 124545124898551398102605833)
      ·
        refine ⟨93408843673913548576954375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124545124898551398102605833 93408843673913548576954375)
        ·
          refine ⟨140113265510870322865431563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93408843673913548576954375 140113265510870322865431563)
          ·
            refine ⟨210169898266305484298147345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140113265510870322865431563 210169898266305484298147345)
            ·
              refine ⟨157627423699729113223610509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210169898266305484298147345 157627423699729113223610509)
              ·
                refine ⟨59110283887398417458853941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157627423699729113223610509 59110283887398417458853941)
                ·
                  refine ⟨5541589114443601636767557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59110283887398417458853941 5541589114443601636767557)
                  ·
                    refine ⟨1039047958958175306893917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541589114443601636767557 1039047958958175306893917)
                    ·
                      rfl

theorem cell23_6070616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_6070616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070616 prefixEnd_6070616 := by exact prefixLift 6070616
  have htrace : WordTrace (prefixWord ++ tailWord_6070616) baseStart_6070616 baseEnd_6070616 := by
    simpa [prefixWord, tailWord_6070616, baseEnd_6070616] using wordTrace_append hprefix tailTrace_6070616
  have hstable : (prefixWord ++ tailWord_6070616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070616).length < 2 ^ (prefixWord ++ tailWord_6070616).sum := by decide
  have hdescent : baseEnd_6070616 < baseStart_6070616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070701 : List Nat := [1, 5, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_6070701 : Nat := 118140960795 + 6070701 * 2 ^ 59
def prefixEnd_6070701 : Nat := 4983230072969 + 3 ^ 40 * 6070701 * 2
def baseEnd_6070701 : Nat := 1039062507576719362706287

theorem tailTrace_6070701 : CollatzResearch.WordTrace tailWord_6070701 prefixEnd_6070701 1039062507576719362706287 := by
  unfold tailWord_6070701
  simp only [CollatzResearch.WordTrace]
  refine ⟨221416655579894545032587957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147611103719929696688391971 221416655579894545032587957)
  ·
    refine ⟨20757811460615113596805121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221416655579894545032587957 20757811460615113596805121)
    ·
      refine ⟨15568358595461335197603841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20757811460615113596805121 15568358595461335197603841)
      ·
        refine ⟨11676268946596001398202881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15568358595461335197603841 11676268946596001398202881)
        ·
          refine ⟨8757201709947001048652161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11676268946596001398202881 8757201709947001048652161)
          ·
            refine ⟨6567901282460250786489121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8757201709947001048652161 6567901282460250786489121)
            ·
              refine ⟨4925925961845188089866841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6567901282460250786489121 4925925961845188089866841)
              ·
                refine ⟨3694444471383891067400131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925925961845188089866841 3694444471383891067400131)
                ·
                  refine ⟨5541666707075836601100197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694444471383891067400131 5541666707075836601100197)
                  ·
                    refine ⟨1039062507576719362706287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541666707075836601100197 1039062507576719362706287)
                    ·
                      rfl

theorem cell23_6070701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_6070701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070701 prefixEnd_6070701 := by exact prefixLift 6070701
  have htrace : WordTrace (prefixWord ++ tailWord_6070701) baseStart_6070701 baseEnd_6070701 := by
    simpa [prefixWord, tailWord_6070701, baseEnd_6070701] using wordTrace_append hprefix tailTrace_6070701
  have hstable : (prefixWord ++ tailWord_6070701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070701).length < 2 ^ (prefixWord ++ tailWord_6070701).sum := by decide
  have hdescent : baseEnd_6070701 < baseStart_6070701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070706 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_6070706 : Nat := 118140960795 + 6070706 * 2 ^ 59
def prefixEnd_6070706 : Nat := 4983230072969 + 3 ^ 40 * 6070706 * 2
def baseEnd_6070706 : Nat := 1039063363377810189518779

theorem tailTrace_6070706 : CollatzResearch.WordTrace tailWord_6070706 prefixEnd_6070706 1039063363377810189518779 := by
  unfold tailWord_6070706
  simp only [CollatzResearch.WordTrace]
  refine ⟨55354209486219107721629993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147611225296584287257679981 55354209486219107721629993)
  ·
    refine ⟨41515657114664330791222495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55354209486219107721629993 41515657114664330791222495)
    ·
      refine ⟨62273485671996496186833743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41515657114664330791222495 62273485671996496186833743)
      ·
        refine ⟨93410228507994744280250615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62273485671996496186833743 93410228507994744280250615)
        ·
          refine ⟨140115342761992116420375923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93410228507994744280250615 140115342761992116420375923)
          ·
            refine ⟨210173014142988174630563885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140115342761992116420375923 210173014142988174630563885)
            ·
              refine ⟨78814880303620565486461457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210173014142988174630563885 78814880303620565486461457)
              ·
                refine ⟨59111160227715424114846093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78814880303620565486461457 59111160227715424114846093)
                ·
                  refine ⟨22166685085393284043067285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59111160227715424114846093 22166685085393284043067285)
                  ·
                    refine ⟨1039063363377810189518779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22166685085393284043067285 1039063363377810189518779)
                    ·
                      rfl

theorem cell23_6070706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_6070706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070706 prefixEnd_6070706 := by exact prefixLift 6070706
  have htrace : WordTrace (prefixWord ++ tailWord_6070706) baseStart_6070706 baseEnd_6070706 := by
    simpa [prefixWord, tailWord_6070706, baseEnd_6070706] using wordTrace_append hprefix tailTrace_6070706
  have hstable : (prefixWord ++ tailWord_6070706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070706).length < 2 ^ (prefixWord ++ tailWord_6070706).sum := by decide
  have hdescent : baseEnd_6070706 < baseStart_6070706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070713 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_6070713 : Nat := 118140960795 + 6070713 * 2 ^ 59
def prefixEnd_6070713 : Nat := 4983230072969 + 3 ^ 40 * 6070713 * 2
def baseEnd_6070713 : Nat := 3117193684498012041168805

theorem tailTrace_6070713 : CollatzResearch.WordTrace tailWord_6070713 prefixEnd_6070713 3117193684498012041168805 := by
  unfold tailWord_6070713
  simp only [CollatzResearch.WordTrace]
  refine ⟨221417093255851071082024793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147611395503900714054683195 221417093255851071082024793)
  ·
    refine ⟨166062819941888303311518595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221417093255851071082024793 166062819941888303311518595)
    ·
      refine ⟨249094229912832454967277893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166062819941888303311518595 249094229912832454967277893)
      ·
        refine ⟨46705168108656085306364605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249094229912832454967277893 46705168108656085306364605)
        ·
          refine ⟨17514438040746031989886727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46705168108656085306364605 17514438040746031989886727)
          ·
            refine ⟨26271657061119047984830091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17514438040746031989886727 26271657061119047984830091)
            ·
              refine ⟨39407485591678571977245137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26271657061119047984830091 39407485591678571977245137)
              ·
                refine ⟨29555614193758928982933853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39407485591678571977245137 29555614193758928982933853)
                ·
                  refine ⟨11083355322659598368600195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29555614193758928982933853 11083355322659598368600195)
                  ·
                    refine ⟨16625032983989397552900293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11083355322659598368600195 16625032983989397552900293)
                    ·
                      refine ⟨3117193684498012041168805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16625032983989397552900293 3117193684498012041168805)
                      ·
                        rfl

theorem cell23_6070713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_6070713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070713 prefixEnd_6070713 := by exact prefixLift 6070713
  have htrace : WordTrace (prefixWord ++ tailWord_6070713) baseStart_6070713 baseEnd_6070713 := by
    simpa [prefixWord, tailWord_6070713, baseEnd_6070713] using wordTrace_append hprefix tailTrace_6070713
  have hstable : (prefixWord ++ tailWord_6070713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070713).length < 2 ^ (prefixWord ++ tailWord_6070713).sum := by decide
  have hdescent : baseEnd_6070713 < baseStart_6070713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070756 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_6070756 : Nat := 118140960795 + 6070756 * 2 ^ 59
def prefixEnd_6070756 : Nat := 4983230072969 + 3 ^ 40 * 6070756 * 2
def baseEnd_6070756 : Nat := 3117215764166155372931107

theorem tailTrace_6070756 : CollatzResearch.WordTrace tailWord_6070756 prefixEnd_6070756 3117215764166155372931107 := by
  unfold tailWord_6070756
  simp only [CollatzResearch.WordTrace]
  refine ⟨110709330797347644712920061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147612441063130192950560081 110709330797347644712920061)
  ·
    refine ⟨41515999049005366767345023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110709330797347644712920061 41515999049005366767345023)
    ·
      refine ⟨62273998573508050151017535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41515999049005366767345023 62273998573508050151017535)
      ·
        refine ⟨93410997860262075226526303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62273998573508050151017535 93410997860262075226526303)
        ·
          refine ⟨140116496790393112839789455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93410997860262075226526303 140116496790393112839789455)
          ·
            refine ⟨210174745185589669259684183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140116496790393112839789455 210174745185589669259684183)
            ·
              refine ⟨315262117778384503889526275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210174745185589669259684183 315262117778384503889526275)
              ·
                refine ⟨472893176667576755834289413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315262117778384503889526275 472893176667576755834289413)
                ·
                  refine ⟨88667470625170641718929265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472893176667576755834289413 88667470625170641718929265)
                  ·
                    refine ⟨66500602968877981289196949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88667470625170641718929265 66500602968877981289196949)
                    ·
                      refine ⟨3117215764166155372931107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66500602968877981289196949 3117215764166155372931107)
                      ·
                        rfl

theorem cell23_6070756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_6070756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070756 prefixEnd_6070756 := by exact prefixLift 6070756
  have htrace : WordTrace (prefixWord ++ tailWord_6070756) baseStart_6070756 baseEnd_6070756 := by
    simpa [prefixWord, tailWord_6070756, baseEnd_6070756] using wordTrace_append hprefix tailTrace_6070756
  have hstable : (prefixWord ++ tailWord_6070756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070756).length < 2 ^ (prefixWord ++ tailWord_6070756).sum := by decide
  have hdescent : baseEnd_6070756 < baseStart_6070756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070833 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_6070833 : Nat := 118140960795 + 6070833 * 2 ^ 59
def prefixEnd_6070833 : Nat := 4983230072969 + 3 ^ 40 * 6070833 * 2
def baseEnd_6070833 : Nat := 3117255302176551571668253

theorem tailTrace_6070833 : CollatzResearch.WordTrace tailWord_6070833 prefixEnd_6070833 3117255302176551571668253 := by
  unfold tailWord_6070833
  simp only [CollatzResearch.WordTrace]
  refine ⟨221421470015416331576393153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147614313343610887717595435 221421470015416331576393153)
  ·
    refine ⟨166066102511562248682294865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221421470015416331576393153 166066102511562248682294865)
    ·
      refine ⟨124549576883671686511721149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166066102511562248682294865 124549576883671686511721149)
      ·
        refine ⟨46706091331376882441895431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124549576883671686511721149 46706091331376882441895431)
        ·
          refine ⟨70059136997065323662843147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46706091331376882441895431 70059136997065323662843147)
          ·
            refine ⟨105088705495597985494264721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70059136997065323662843147 105088705495597985494264721)
            ·
              refine ⟨78816529121698489120698541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105088705495597985494264721 78816529121698489120698541)
              ·
                refine ⟨29556198420636933420261953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78816529121698489120698541 29556198420636933420261953)
                ·
                  refine ⟨22167148815477700065196465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29556198420636933420261953 22167148815477700065196465)
                  ·
                    refine ⟨16625361611608275048897349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22167148815477700065196465 16625361611608275048897349)
                    ·
                      refine ⟨3117255302176551571668253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16625361611608275048897349 3117255302176551571668253)
                      ·
                        rfl

theorem cell23_6070833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_6070833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070833 prefixEnd_6070833 := by exact prefixLift 6070833
  have htrace : WordTrace (prefixWord ++ tailWord_6070833) baseStart_6070833 baseEnd_6070833 := by
    simpa [prefixWord, tailWord_6070833, baseEnd_6070833] using wordTrace_append hprefix tailTrace_6070833
  have hstable : (prefixWord ++ tailWord_6070833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070833).length < 2 ^ (prefixWord ++ tailWord_6070833).sum := by decide
  have hdescent : baseEnd_6070833 < baseStart_6070833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070854 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6070854 : Nat := 118140960795 + 6070854 * 2 ^ 59
def prefixEnd_6070854 : Nat := 4983230072969 + 3 ^ 40 * 6070854 * 2
def baseEnd_6070854 : Nat := 3117266085270295989505657

theorem tailTrace_6070854 : CollatzResearch.WordTrace tailWord_6070854 prefixEnd_6070854 3117266085270295989505657 := by
  unfold tailWord_6070854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919444873385632880090863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147614823965560168108605077 6919444873385632880090863)
  ·
    refine ⟨10379167310078449320136295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919444873385632880090863 10379167310078449320136295)
    ·
      refine ⟨15568750965117673980204443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10379167310078449320136295 15568750965117673980204443)
      ·
        refine ⟨23353126447676510970306665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15568750965117673980204443 23353126447676510970306665)
        ·
          refine ⟨17514844835757383227729999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23353126447676510970306665 17514844835757383227729999)
          ·
            refine ⟨26272267253636074841594999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17514844835757383227729999 26272267253636074841594999)
            ·
              refine ⟨39408400880454112262392499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26272267253636074841594999 39408400880454112262392499)
              ·
                refine ⟨59112601320681168393588749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39408400880454112262392499 59112601320681168393588749)
                ·
                  refine ⟨22167225495255438147595781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59112601320681168393588749 22167225495255438147595781)
                  ·
                    refine ⟨4156354780360394652674209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22167225495255438147595781 4156354780360394652674209)
                    ·
                      refine ⟨3117266085270295989505657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156354780360394652674209 3117266085270295989505657)
                      ·
                        rfl

theorem cell23_6070854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6070854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070854 prefixEnd_6070854 := by exact prefixLift 6070854
  have htrace : WordTrace (prefixWord ++ tailWord_6070854) baseStart_6070854 baseEnd_6070854 := by
    simpa [prefixWord, tailWord_6070854, baseEnd_6070854] using wordTrace_append hprefix tailTrace_6070854
  have hstable : (prefixWord ++ tailWord_6070854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070854).length < 2 ^ (prefixWord ++ tailWord_6070854).sum := by decide
  have hdescent : baseEnd_6070854 < baseStart_6070854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070860 : List Nat := [2, 2, 1, 3, 1, 2, 2, 5, 5]
def baseStart_6070860 : Nat := 118140960795 + 6070860 * 2 ^ 59
def prefixEnd_6070860 : Nat := 4983230072969 + 3 ^ 40 * 6070860 * 2
def baseEnd_6070860 : Nat := 346363240683802551781181

theorem tailTrace_6070860 : CollatzResearch.WordTrace tailWord_6070860 prefixEnd_6070860 346363240683802551781181 := by
  unfold tailWord_6070860
  simp only [CollatzResearch.WordTrace]
  refine ⟨110711227393159257593813017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147614969857545676791750689 110711227393159257593813017)
  ·
    refine ⟨83033420544869443195359763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110711227393159257593813017 83033420544869443195359763)
    ·
      refine ⟨124550130817304164793039645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83033420544869443195359763 124550130817304164793039645)
      ·
        refine ⟨46706299056489061797389867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124550130817304164793039645 46706299056489061797389867)
        ·
          refine ⟨70059448584733592696084801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46706299056489061797389867 70059448584733592696084801)
          ·
            refine ⟨52544586438550194522063601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70059448584733592696084801 52544586438550194522063601)
            ·
              refine ⟨39408439828912645891547701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52544586438550194522063601 39408439828912645891547701)
              ·
                refine ⟨3694541233960560552332597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39408439828912645891547701 3694541233960560552332597)
                ·
                  refine ⟨346363240683802551781181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3694541233960560552332597 346363240683802551781181)
                  ·
                    rfl

theorem cell23_6070860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_6070860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070860 prefixEnd_6070860 := by exact prefixLift 6070860
  have htrace : WordTrace (prefixWord ++ tailWord_6070860) baseStart_6070860 baseEnd_6070860 := by
    simpa [prefixWord, tailWord_6070860, baseEnd_6070860] using wordTrace_append hprefix tailTrace_6070860
  have hstable : (prefixWord ++ tailWord_6070860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070860).length < 2 ^ (prefixWord ++ tailWord_6070860).sum := by decide
  have hdescent : baseEnd_6070860 < baseStart_6070860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070880 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 2, 5, 2]
def baseStart_6070880 : Nat := 118140960795 + 6070880 * 2 ^ 59
def prefixEnd_6070880 : Nat := 4983230072969 + 3 ^ 40 * 6070880 * 2
def baseEnd_6070880 : Nat := 3117279435767312887780537

theorem tailTrace_6070880 : CollatzResearch.WordTrace tailWord_6070880 prefixEnd_6070880 3117279435767312887780537 := by
  unfold tailWord_6070880
  simp only [CollatzResearch.WordTrace]
  refine ⟨110711592123123029301677047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147615456164164039068902729 110711592123123029301677047)
  ·
    refine ⟨166067388184684543952515571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110711592123123029301677047 166067388184684543952515571)
    ·
      refine ⟨249101082277026815928773357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166067388184684543952515571 249101082277026815928773357)
      ·
        refine ⟨93412905853885055973290009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249101082277026815928773357 93412905853885055973290009)
        ·
          refine ⟨70059679390413791979967507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93412905853885055973290009 70059679390413791979967507)
          ·
            refine ⟨105089519085620687969951261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70059679390413791979967507 105089519085620687969951261)
            ·
              refine ⟨39408569657107757988731723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105089519085620687969951261 39408569657107757988731723)
              ·
                refine ⟨59112854485661636983097585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39408569657107757988731723 59112854485661636983097585)
                ·
                  refine ⟨44334640864246227737323189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59112854485661636983097585 44334640864246227737323189)
                  ·
                    refine ⟨4156372581023083850374049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44334640864246227737323189 4156372581023083850374049)
                    ·
                      refine ⟨3117279435767312887780537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156372581023083850374049 3117279435767312887780537)
                      ·
                        rfl

theorem cell23_6070880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_6070880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070880 prefixEnd_6070880 := by exact prefixLift 6070880
  have htrace : WordTrace (prefixWord ++ tailWord_6070880) baseStart_6070880 baseEnd_6070880 := by
    simpa [prefixWord, tailWord_6070880, baseEnd_6070880] using wordTrace_append hprefix tailTrace_6070880
  have hstable : (prefixWord ++ tailWord_6070880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070880).length < 2 ^ (prefixWord ++ tailWord_6070880).sum := by decide
  have hdescent : baseEnd_6070880 < baseStart_6070880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070883 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5]
def baseStart_6070883 : Nat := 118140960795 + 6070883 * 2 ^ 59
def prefixEnd_6070883 : Nat := 4983230072969 + 3 ^ 40 * 6070883 * 2
def baseEnd_6070883 : Nat := 3117280976209276376043023

theorem tailTrace_6070883 : CollatzResearch.WordTrace tailWord_6070883 prefixEnd_6070883 3117280976209276376043023 := by
  unfold tailWord_6070883
  simp only [CollatzResearch.WordTrace]
  refine ⟨221423293665235190115713303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147615529110156793410475535 221423293665235190115713303)
  ·
    refine ⟨332134940497852785173569955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221423293665235190115713303 332134940497852785173569955)
    ·
      refine ⟨498202410746779177760354933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332134940497852785173569955 498202410746779177760354933)
      ·
        refine ⟨46706476007510547915033275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 498202410746779177760354933 46706476007510547915033275)
        ·
          refine ⟨70059714011265821872549913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46706476007510547915033275 70059714011265821872549913)
          ·
            refine ⟨52544785508449366404412435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70059714011265821872549913 52544785508449366404412435)
            ·
              refine ⟨78817178262674049606618653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52544785508449366404412435 78817178262674049606618653)
              ·
                refine ⟨29556441848502768602481995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78817178262674049606618653 29556441848502768602481995)
                ·
                  refine ⟨44334662772754152903722993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29556441848502768602481995 44334662772754152903722993)
                  ·
                    refine ⟨33250997079565614677792245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44334662772754152903722993 33250997079565614677792245)
                    ·
                      refine ⟨3117280976209276376043023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33250997079565614677792245 3117280976209276376043023)
                      ·
                        rfl

theorem cell23_6070883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_6070883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070883 prefixEnd_6070883 := by exact prefixLift 6070883
  have htrace : WordTrace (prefixWord ++ tailWord_6070883) baseStart_6070883 baseEnd_6070883 := by
    simpa [prefixWord, tailWord_6070883, baseEnd_6070883] using wordTrace_append hprefix tailTrace_6070883
  have hstable : (prefixWord ++ tailWord_6070883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070883).length < 2 ^ (prefixWord ++ tailWord_6070883).sum := by decide
  have hdescent : baseEnd_6070883 < baseStart_6070883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6070937 : List Nat := [1, 2, 1, 2, 1, 2, 3, 6, 1, 4]
def baseStart_6070937 : Nat := 118140960795 + 6070937 * 2 ^ 59
def prefixEnd_6070937 : Nat := 4983230072969 + 3 ^ 40 * 6070937 * 2
def baseEnd_6070937 : Nat := 1039102901388206388255925

theorem tailTrace_6070937 : CollatzResearch.WordTrace tailWord_6070937 prefixEnd_6070937 1039102901388206388255925 := by
  unfold tailWord_6070937
  simp only [CollatzResearch.WordTrace]
  refine ⟨221425263207039557338179065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147616842138026371558786043 221425263207039557338179065)
  ·
    refine ⟨166068947405279668003634299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221425263207039557338179065 166068947405279668003634299)
    ·
      refine ⟨249103421107919502005451449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166068947405279668003634299 249103421107919502005451449)
      ·
        refine ⟨186827565830939626504088587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249103421107919502005451449 186827565830939626504088587)
        ·
          refine ⟨280241348746409439756132881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186827565830939626504088587 280241348746409439756132881)
          ·
            refine ⟨210181011559807079817099661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280241348746409439756132881 210181011559807079817099661)
            ·
              refine ⟨78817879334927654931412373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210181011559807079817099661 78817879334927654931412373)
              ·
                refine ⟨3694588093824733824909955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78817879334927654931412373 3694588093824733824909955)
                ·
                  refine ⟨5541882140737100737364933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694588093824733824909955 5541882140737100737364933)
                  ·
                    refine ⟨1039102901388206388255925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541882140737100737364933 1039102901388206388255925)
                    ·
                      rfl

theorem cell23_6070937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 4].length) (baseStart_6070937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6070937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6070937 prefixEnd_6070937 := by exact prefixLift 6070937
  have htrace : WordTrace (prefixWord ++ tailWord_6070937) baseStart_6070937 baseEnd_6070937 := by
    simpa [prefixWord, tailWord_6070937, baseEnd_6070937] using wordTrace_append hprefix tailTrace_6070937
  have hstable : (prefixWord ++ tailWord_6070937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6070937).length < 2 ^ (prefixWord ++ tailWord_6070937).sum := by decide
  have hdescent : baseEnd_6070937 < baseStart_6070937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6070937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071017 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 4]
def baseStart_6071017 : Nat := 118140960795 + 6071017 * 2 ^ 59
def prefixEnd_6071017 : Nat := 4983230072969 + 3 ^ 40 * 6071017 * 2
def baseEnd_6071017 : Nat := 3117349782616978851767407

theorem tailTrace_6071017 : CollatzResearch.WordTrace tailWord_6071017 prefixEnd_6071017 3117349782616978851767407 := by
  unfold tailWord_6071017
  simp only [CollatzResearch.WordTrace]
  refine ⟨221428181046749731001091305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147618787364499820667394203 221428181046749731001091305)
  ·
    refine ⟨166071135785062298250818479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221428181046749731001091305 166071135785062298250818479)
    ·
      refine ⟨249106703677593447376227719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166071135785062298250818479 249106703677593447376227719)
      ·
        refine ⟨373660055516390171064341579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249106703677593447376227719 373660055516390171064341579)
        ·
          refine ⟨560490083274585256596512369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373660055516390171064341579 560490083274585256596512369)
          ·
            refine ⟨420367562455938942447384277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560490083274585256596512369 420367562455938942447384277)
            ·
              refine ⟨9852364745061068963610569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 420367562455938942447384277 9852364745061068963610569)
              ·
                refine ⟨7389273558795801722707927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9852364745061068963610569 7389273558795801722707927)
                ·
                  refine ⟨11083910338193702584061891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7389273558795801722707927 11083910338193702584061891)
                  ·
                    refine ⟨16625865507290553876092837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11083910338193702584061891 16625865507290553876092837)
                    ·
                      refine ⟨3117349782616978851767407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16625865507290553876092837 3117349782616978851767407)
                      ·
                        rfl

theorem cell23_6071017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_6071017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071017 prefixEnd_6071017 := by exact prefixLift 6071017
  have htrace : WordTrace (prefixWord ++ tailWord_6071017) baseStart_6071017 baseEnd_6071017 := by
    simpa [prefixWord, tailWord_6071017, baseEnd_6071017] using wordTrace_append hprefix tailTrace_6071017
  have hstable : (prefixWord ++ tailWord_6071017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071017).length < 2 ^ (prefixWord ++ tailWord_6071017).sum := by decide
  have hdescent : baseEnd_6071017 < baseStart_6071017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071044 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_6071044 : Nat := 118140960795 + 6071044 * 2 ^ 59
def prefixEnd_6071044 : Nat := 4983230072969 + 3 ^ 40 * 6071044 * 2
def baseEnd_6071044 : Nat := 1039121215531550082043261

theorem tailTrace_6071044 : CollatzResearch.WordTrace tailWord_6071044 prefixEnd_6071044 1039121215531550082043261 := by
  unfold tailWord_6071044
  simp only [CollatzResearch.WordTrace]
  refine ⟨110714582908825957306162093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147619443878434609741549457 110714582908825957306162093)
  ·
    refine ⟨41517968590809733989810785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110714582908825957306162093 41517968590809733989810785)
    ·
      refine ⟨31138476443107300492358089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41517968590809733989810785 31138476443107300492358089)
      ·
        refine ⟨23353857332330475369268567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31138476443107300492358089 23353857332330475369268567)
        ·
          refine ⟨35030785998495713053902851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23353857332330475369268567 35030785998495713053902851)
          ·
            refine ⟨52546178997743569580854277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35030785998495713053902851 52546178997743569580854277)
            ·
              refine ⟨9852408562076919296410177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52546178997743569580854277 9852408562076919296410177)
              ·
                refine ⟨7389306421557689472307633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9852408562076919296410177 7389306421557689472307633)
                ·
                  refine ⟨5541979816168267104230725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389306421557689472307633 5541979816168267104230725)
                  ·
                    refine ⟨1039121215531550082043261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5541979816168267104230725 1039121215531550082043261)
                    ·
                      rfl

theorem cell23_6071044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_6071044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071044 prefixEnd_6071044 := by exact prefixLift 6071044
  have htrace : WordTrace (prefixWord ++ tailWord_6071044) baseStart_6071044 baseEnd_6071044 := by
    simpa [prefixWord, tailWord_6071044, baseEnd_6071044] using wordTrace_append hprefix tailTrace_6071044
  have hstable : (prefixWord ++ tailWord_6071044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071044).length < 2 ^ (prefixWord ++ tailWord_6071044).sum := by decide
  have hdescent : baseEnd_6071044 < baseStart_6071044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071085 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6071085 : Nat := 118140960795 + 6071085 * 2 ^ 59
def prefixEnd_6071085 : Nat := 4983230072969 + 3 ^ 40 * 6071085 * 2
def baseEnd_6071085 : Nat := 3117384699301484585717095

theorem tailTrace_6071085 : CollatzResearch.WordTrace tailWord_6071085 prefixEnd_6071085 3117384699301484585717095 := by
  unfold tailWord_6071085
  simp only [CollatzResearch.WordTrace]
  refine ⟨221430661210503378614566709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147620440807002252409711139 221430661210503378614566709)
  ·
    refine ⟨20759124488484691745115629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 221430661210503378614566709 20759124488484691745115629)
    ·
      refine ⟨7784671683181759404418361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20759124488484691745115629 7784671683181759404418361)
      ·
        refine ⟨5838503762386319553313771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7784671683181759404418361 5838503762386319553313771)
        ·
          refine ⟨8757755643579479329970657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5838503762386319553313771 8757755643579479329970657)
          ·
            refine ⟨6568316732684609497477993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8757755643579479329970657 6568316732684609497477993)
            ·
              refine ⟨4926237549513457123108495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6568316732684609497477993 4926237549513457123108495)
              ·
                refine ⟨7389356324270185684662743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926237549513457123108495 7389356324270185684662743)
                ·
                  refine ⟨11084034486405278526994115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7389356324270185684662743 11084034486405278526994115)
                  ·
                    refine ⟨16626051729607917790491173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11084034486405278526994115 16626051729607917790491173)
                    ·
                      refine ⟨3117384699301484585717095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16626051729607917790491173 3117384699301484585717095)
                      ·
                        rfl

theorem cell23_6071085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6071085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071085 prefixEnd_6071085 := by exact prefixLift 6071085
  have htrace : WordTrace (prefixWord ++ tailWord_6071085) baseStart_6071085 baseEnd_6071085 := by
    simpa [prefixWord, tailWord_6071085, baseEnd_6071085] using wordTrace_append hprefix tailTrace_6071085
  have hstable : (prefixWord ++ tailWord_6071085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071085).length < 2 ^ (prefixWord ++ tailWord_6071085).sum := by decide
  have hdescent : baseEnd_6071085 < baseStart_6071085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071101 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6071101 : Nat := 118140960795 + 6071101 * 2 ^ 59
def prefixEnd_6071101 : Nat := 4983230072969 + 3 ^ 40 * 6071101 * 2
def baseEnd_6071101 : Nat := 3117392914991956523117021

theorem tailTrace_6071101 : CollatzResearch.WordTrace tailWord_6071101 prefixEnd_6071101 3117392914991956523117021 := by
  unfold tailWord_6071101
  simp only [CollatzResearch.WordTrace]
  refine ⟨221431244778445413347149157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147620829852296942231432771 221431244778445413347149157)
  ·
    refine ⟨41518358395958515002590467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221431244778445413347149157 41518358395958515002590467)
    ·
      refine ⟨62277537593937772503885701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41518358395958515002590467 62277537593937772503885701)
      ·
        refine ⟨11677038298863332344478569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62277537593937772503885701 11677038298863332344478569)
        ·
          refine ⟨8757778724147499258358927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11677038298863332344478569 8757778724147499258358927)
          ·
            refine ⟨13136668086221248887538391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8757778724147499258358927 13136668086221248887538391)
            ·
              refine ⟨19705002129331873331307587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13136668086221248887538391 19705002129331873331307587)
              ·
                refine ⟨29557503193997809996961381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19705002129331873331307587 29557503193997809996961381)
                ·
                  refine ⟨5542031848874589374430259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29557503193997809996961381 5542031848874589374430259)
                  ·
                    refine ⟨8313047773311884061645389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5542031848874589374430259 8313047773311884061645389)
                    ·
                      refine ⟨3117392914991956523117021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8313047773311884061645389 3117392914991956523117021)
                      ·
                        rfl

theorem cell23_6071101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6071101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071101 prefixEnd_6071101 := by exact prefixLift 6071101
  have htrace : WordTrace (prefixWord ++ tailWord_6071101) baseStart_6071101 baseEnd_6071101 := by
    simpa [prefixWord, tailWord_6071101, baseEnd_6071101] using wordTrace_append hprefix tailTrace_6071101
  have hstable : (prefixWord ++ tailWord_6071101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071101).length < 2 ^ (prefixWord ++ tailWord_6071101).sum := by decide
  have hdescent : baseEnd_6071101 < baseStart_6071101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071158 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_6071158 : Nat := 118140960795 + 6071158 * 2 ^ 59
def prefixEnd_6071158 : Nat := 4983230072969 + 3 ^ 40 * 6071158 * 2
def baseEnd_6071158 : Nat := 3117422183389262800104259

theorem tailTrace_6071158 : CollatzResearch.WordTrace tailWord_6071158 prefixEnd_6071158 3117422183389262800104259 := by
  unfold tailWord_6071158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13839582733702432005123383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147622215826159274721316085 13839582733702432005123383)
  ·
    refine ⟨20759374100553648007685075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13839582733702432005123383 20759374100553648007685075)
    ·
      refine ⟨31139061150830472011527613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20759374100553648007685075 31139061150830472011527613)
      ·
        refine ⟨11677147931561427004322855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31139061150830472011527613 11677147931561427004322855)
        ·
          refine ⟨17515721897342140506484283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11677147931561427004322855 17515721897342140506484283)
          ·
            refine ⟨26273582846013210759726425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17515721897342140506484283 26273582846013210759726425)
            ·
              refine ⟨19705187134509908069794819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26273582846013210759726425 19705187134509908069794819)
              ·
                refine ⟨29557780701764862104692229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19705187134509908069794819 29557780701764862104692229)
                ·
                  refine ⟨5542083881580911644629793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29557780701764862104692229 5542083881580911644629793)
                  ·
                    refine ⟨4156562911185683733472345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5542083881580911644629793 4156562911185683733472345)
                    ·
                      refine ⟨3117422183389262800104259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156562911185683733472345 3117422183389262800104259)
                      ·
                        rfl

theorem cell23_6071158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_6071158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071158 prefixEnd_6071158 := by exact prefixLift 6071158
  have htrace : WordTrace (prefixWord ++ tailWord_6071158) baseStart_6071158 baseEnd_6071158 := by
    simpa [prefixWord, tailWord_6071158, baseEnd_6071158] using wordTrace_append hprefix tailTrace_6071158
  have hstable : (prefixWord ++ tailWord_6071158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071158).length < 2 ^ (prefixWord ++ tailWord_6071158).sum := by decide
  have hdescent : baseEnd_6071158 < baseStart_6071158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071160 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 3, 7]
def baseStart_6071160 : Nat := 118140960795 + 6071160 * 2 ^ 59
def prefixEnd_6071160 : Nat := 4983230072969 + 3 ^ 40 * 6071160 * 2
def baseEnd_6071160 : Nat := 1039141070116857264093083

theorem tailTrace_6071160 : CollatzResearch.WordTrace tailWord_6071160 prefixEnd_6071160 1039141070116857264093083 := by
  unfold tailWord_6071160
  simp only [CollatzResearch.WordTrace]
  refine ⟨110716698342615833211773467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147622264456821110949031289 110716698342615833211773467)
  ·
    refine ⟨166075047513923749817660201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110716698342615833211773467 166075047513923749817660201)
    ·
      refine ⟨124556285635442812363245151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166075047513923749817660201 124556285635442812363245151)
      ·
        refine ⟨186834428453164218544867727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124556285635442812363245151 186834428453164218544867727)
        ·
          refine ⟨280251642679746327817301591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186834428453164218544867727 280251642679746327817301591)
          ·
            refine ⟨420377464019619491725952387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280251642679746327817301591 420377464019619491725952387)
            ·
              refine ⟨630566196029429237588928581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420377464019619491725952387 630566196029429237588928581)
              ·
                refine ⟨118231161755517982047924109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630566196029429237588928581 118231161755517982047924109)
                ·
                  refine ⟨44336685658319243267971541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118231161755517982047924109 44336685658319243267971541)
                  ·
                    refine ⟨1039141070116857264093083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44336685658319243267971541 1039141070116857264093083)
                    ·
                      rfl

theorem cell23_6071160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_6071160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071160 prefixEnd_6071160 := by exact prefixLift 6071160
  have htrace : WordTrace (prefixWord ++ tailWord_6071160) baseStart_6071160 baseEnd_6071160 := by
    simpa [prefixWord, tailWord_6071160, baseEnd_6071160] using wordTrace_append hprefix tailTrace_6071160
  have hstable : (prefixWord ++ tailWord_6071160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071160).length < 2 ^ (prefixWord ++ tailWord_6071160).sum := by decide
  have hdescent : baseEnd_6071160 < baseStart_6071160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071175 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_6071175 : Nat := 118140960795 + 6071175 * 2 ^ 59
def prefixEnd_6071175 : Nat := 4983230072969 + 3 ^ 40 * 6071175 * 2
def baseEnd_6071175 : Nat := 3117430912560389233591681

theorem tailTrace_6071175 : CollatzResearch.WordTrace tailWord_6071175 prefixEnd_6071175 3117430912560389233591681 := by
  unfold tailWord_6071175
  simp only [CollatzResearch.WordTrace]
  refine ⟨221433943780177323985342979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147622629186784882656895319 221433943780177323985342979)
  ·
    refine ⟨332150915670265985978014469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221433943780177323985342979 332150915670265985978014469)
    ·
      refine ⟨62278296688174872370877713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332150915670265985978014469 62278296688174872370877713)
      ·
        refine ⟨46708722516131154278158285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62278296688174872370877713 46708722516131154278158285)
        ·
          refine ⟨17515770943549182854309357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46708722516131154278158285 17515770943549182854309357)
          ·
            refine ⟨6568414103830943570366009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17515770943549182854309357 6568414103830943570366009)
            ·
              refine ⟨4926310577873207677774507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6568414103830943570366009 4926310577873207677774507)
              ·
                refine ⟨7389465866809811516661761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926310577873207677774507 7389465866809811516661761)
                ·
                  refine ⟨5542099400107358637496321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389465866809811516661761 5542099400107358637496321)
                  ·
                    refine ⟨4156574550080518978122241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5542099400107358637496321 4156574550080518978122241)
                    ·
                      refine ⟨3117430912560389233591681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156574550080518978122241 3117430912560389233591681)
                      ·
                        rfl

theorem cell23_6071175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_6071175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071175 prefixEnd_6071175 := by exact prefixLift 6071175
  have htrace : WordTrace (prefixWord ++ tailWord_6071175) baseStart_6071175 baseEnd_6071175 := by
    simpa [prefixWord, tailWord_6071175, baseEnd_6071175] using wordTrace_append hprefix tailTrace_6071175
  have hstable : (prefixWord ++ tailWord_6071175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071175).length < 2 ^ (prefixWord ++ tailWord_6071175).sum := by decide
  have hdescent : baseEnd_6071175 < baseStart_6071175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071258 : List Nat := [3, 1, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_6071258 : Nat := 118140960795 + 6071258 * 2 ^ 59
def prefixEnd_6071258 : Nat := 4983230072969 + 3 ^ 40 * 6071258 * 2
def baseEnd_6071258 : Nat := 1039157843818237469617933

theorem tailTrace_6071258 : CollatzResearch.WordTrace tailWord_6071258 prefixEnd_6071258 1039157843818237469617933 := by
  unfold tailWord_6071258
  simp only [CollatzResearch.WordTrace]
  refine ⟨55359242759719157290153607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147624647359251086107076285 55359242759719157290153607)
  ·
    refine ⟨83038864139578735935230411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55359242759719157290153607 83038864139578735935230411)
    ·
      refine ⟨124558296209368103902845617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83038864139578735935230411 124558296209368103902845617)
      ·
        refine ⟨93418722157026077927134213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124558296209368103902845617 93418722157026077927134213)
        ·
          refine ⟨17516010404442389611337665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93418722157026077927134213 17516010404442389611337665)
          ·
            refine ⟨13137007803331792208503249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17516010404442389611337665 13137007803331792208503249)
            ·
              refine ⟨9852755852498844156377437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13137007803331792208503249 9852755852498844156377437)
              ·
                refine ⟨3694783444687066558641539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9852755852498844156377437 3694783444687066558641539)
                ·
                  refine ⟨5542175167030599837962309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694783444687066558641539 5542175167030599837962309)
                  ·
                    refine ⟨1039157843818237469617933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5542175167030599837962309 1039157843818237469617933)
                    ·
                      rfl

theorem cell23_6071258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_6071258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071258 prefixEnd_6071258 := by exact prefixLift 6071258
  have htrace : WordTrace (prefixWord ++ tailWord_6071258) baseStart_6071258 baseEnd_6071258 := by
    simpa [prefixWord, tailWord_6071258, baseEnd_6071258] using wordTrace_append hprefix tailTrace_6071258
  have hstable : (prefixWord ++ tailWord_6071258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071258).length < 2 ^ (prefixWord ++ tailWord_6071258).sum := by decide
  have hdescent : baseEnd_6071258 < baseStart_6071258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071271 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 6]
def baseStart_6071271 : Nat := 118140960795 + 6071271 * 2 ^ 59
def prefixEnd_6071271 : Nat := 4983230072969 + 3 ^ 40 * 6071271 * 2
def baseEnd_6071271 : Nat := 346386689633691206443471

theorem tailTrace_6071271 : CollatzResearch.WordTrace tailWord_6071271 prefixEnd_6071271 346386689633691206443471 := by
  unfold tailWord_6071271
  simp only [CollatzResearch.WordTrace]
  refine ⟨221437445187829532380837667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147624963458553021587225111 221437445187829532380837667)
  ·
    refine ⟨332156167781744298571256501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221437445187829532380837667 332156167781744298571256501)
    ·
      refine ⟨31139640729538527991055297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 332156167781744298571256501 31139640729538527991055297)
      ·
        refine ⟨23354730547153895993291473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31139640729538527991055297 23354730547153895993291473)
        ·
          refine ⟨17516047910365421994968605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23354730547153895993291473 17516047910365421994968605)
          ·
            refine ⟨6568517966387033248113227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17516047910365421994968605 6568517966387033248113227)
            ·
              refine ⟨9852776949580549872169841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568517966387033248113227 9852776949580549872169841)
              ·
                refine ⟨7389582712185412404127381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9852776949580549872169841 7389582712185412404127381)
                ·
                  refine ⟨346386689633691206443471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7389582712185412404127381 346386689633691206443471)
                  ·
                    rfl

theorem cell23_6071271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 6].length) (baseStart_6071271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071271 prefixEnd_6071271 := by exact prefixLift 6071271
  have htrace : WordTrace (prefixWord ++ tailWord_6071271) baseStart_6071271 baseEnd_6071271 := by
    simpa [prefixWord, tailWord_6071271, baseEnd_6071271] using wordTrace_append hprefix tailTrace_6071271
  have hstable : (prefixWord ++ tailWord_6071271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071271).length < 2 ^ (prefixWord ++ tailWord_6071271).sum := by decide
  have hdescent : baseEnd_6071271 < baseStart_6071271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071281 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_6071281 : Nat := 118140960795 + 6071281 * 2 ^ 59
def prefixEnd_6071281 : Nat := 4983230072969 + 3 ^ 40 * 6071281 * 2
def baseEnd_6071281 : Nat := 3117485341509765818866193

theorem tailTrace_6071281 : CollatzResearch.WordTrace tailWord_6071281 prefixEnd_6071281 3117485341509765818866193 := by
  unfold tailWord_6071281
  simp only [CollatzResearch.WordTrace]
  refine ⟨221437809917793304088701697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147625206611862202725801131 221437809917793304088701697)
  ·
    refine ⟨166078357438344978066526273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221437809917793304088701697 166078357438344978066526273)
    ·
      refine ⟨124558768078758733549894705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166078357438344978066526273 124558768078758733549894705)
      ·
        refine ⟨93419076059069050162421029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124558768078758733549894705 93419076059069050162421029)
        ·
          refine ⟨17516076761075446905453943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93419076059069050162421029 17516076761075446905453943)
          ·
            refine ⟨26274115141613170358180915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17516076761075446905453943 26274115141613170358180915)
            ·
              refine ⟨39411172712419755537271373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26274115141613170358180915 39411172712419755537271373)
              ·
                refine ⟨14779189767157408326476765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39411172712419755537271373 14779189767157408326476765)
                ·
                  refine ⟨5542196162684028122428787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14779189767157408326476765 5542196162684028122428787)
                  ·
                    refine ⟨8313294244026042183643181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5542196162684028122428787 8313294244026042183643181)
                    ·
                      refine ⟨3117485341509765818866193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8313294244026042183643181 3117485341509765818866193)
                      ·
                        rfl

theorem cell23_6071281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_6071281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071281 prefixEnd_6071281 := by exact prefixLift 6071281
  have htrace : WordTrace (prefixWord ++ tailWord_6071281) baseStart_6071281 baseEnd_6071281 := by
    simpa [prefixWord, tailWord_6071281, baseEnd_6071281] using wordTrace_append hprefix tailTrace_6071281
  have hstable : (prefixWord ++ tailWord_6071281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071281).length < 2 ^ (prefixWord ++ tailWord_6071281).sum := by decide
  have hdescent : baseEnd_6071281 < baseStart_6071281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071321 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 5, 2, 2]
def baseStart_6071321 : Nat := 118140960795 + 6071321 * 2 ^ 59
def prefixEnd_6071321 : Nat := 4983230072969 + 3 ^ 40 * 6071321 * 2
def baseEnd_6071321 : Nat := 3117505880735945662366009

theorem tailTrace_6071321 : CollatzResearch.WordTrace tailWord_6071321 prefixEnd_6071321 3117505880735945662366009 := by
  unfold tailWord_6071321
  simp only [CollatzResearch.WordTrace]
  refine ⟨221439268837648390920157817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147626179225098927280105211 221439268837648390920157817)
  ·
    refine ⟨166079451628236293190118363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221439268837648390920157817 166079451628236293190118363)
    ·
      refine ⟨249119177442354439785177545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166079451628236293190118363 249119177442354439785177545)
      ·
        refine ⟨186839383081765829838883159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249119177442354439785177545 186839383081765829838883159)
        ·
          refine ⟨280259074622648744758324739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186839383081765829838883159 280259074622648744758324739)
          ·
            refine ⟨420388611933973117137487109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280259074622648744758324739 420388611933973117137487109)
            ·
              refine ⟨78822864737619959463278833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 420388611933973117137487109 78822864737619959463278833)
              ·
                refine ⟨59117148553214969597459125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78822864737619959463278833 59117148553214969597459125)
                ·
                  refine ⟨5542232676863903399761793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59117148553214969597459125 5542232676863903399761793)
                  ·
                    refine ⟨4156674507647927549821345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5542232676863903399761793 4156674507647927549821345)
                    ·
                      refine ⟨3117505880735945662366009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156674507647927549821345 3117505880735945662366009)
                      ·
                        rfl

theorem cell23_6071321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_6071321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071321 prefixEnd_6071321 := by exact prefixLift 6071321
  have htrace : WordTrace (prefixWord ++ tailWord_6071321) baseStart_6071321 baseEnd_6071321 := by
    simpa [prefixWord, tailWord_6071321, baseEnd_6071321] using wordTrace_append hprefix tailTrace_6071321
  have hstable : (prefixWord ++ tailWord_6071321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071321).length < 2 ^ (prefixWord ++ tailWord_6071321).sum := by decide
  have hdescent : baseEnd_6071321 < baseStart_6071321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071327 : List Nat := [1, 1, 2, 4, 1, 3, 11]
def baseStart_6071327 : Nat := 118140960795 + 6071327 * 2 ^ 59
def prefixEnd_6071327 : Nat := 4983230072969 + 3 ^ 40 * 6071327 * 2
def baseEnd_6071327 : Nat := 38487764958270032578901

theorem tailTrace_6071327 : CollatzResearch.WordTrace tailWord_6071327 prefixEnd_6071327 38487764958270032578901 := by
  unfold tailWord_6071327
  simp only [CollatzResearch.WordTrace]
  refine ⟨221439487675626653944876235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147626325117084435963250823 221439487675626653944876235)
  ·
    refine ⟨332159231513439980917314353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221439487675626653944876235 332159231513439980917314353)
    ·
      refine ⟨249119423635079985687985765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332159231513439980917314353 249119423635079985687985765)
      ·
        refine ⟨46709891931577497316497331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249119423635079985687985765 46709891931577497316497331)
        ·
          refine ⟨70064837897366245974745997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46709891931577497316497331 70064837897366245974745997)
          ·
            refine ⟨26274314211512342240529749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70064837897366245974745997 26274314211512342240529749)
            ·
              refine ⟨38487764958270032578901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26274314211512342240529749 38487764958270032578901)
              ·
                rfl

theorem cell23_6071327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 11].length) (baseStart_6071327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071327 prefixEnd_6071327 := by exact prefixLift 6071327
  have htrace : WordTrace (prefixWord ++ tailWord_6071327) baseStart_6071327 baseEnd_6071327 := by
    simpa [prefixWord, tailWord_6071327, baseEnd_6071327] using wordTrace_append hprefix tailTrace_6071327
  have hstable : (prefixWord ++ tailWord_6071327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071327).length < 2 ^ (prefixWord ++ tailWord_6071327).sum := by decide
  have hdescent : baseEnd_6071327 < baseStart_6071327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071332 : List Nat := [2, 3, 1, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6071332 : Nat := 118140960795 + 6071332 * 2 ^ 59
def prefixEnd_6071332 : Nat := 4983230072969 + 3 ^ 40 * 6071332 * 2
def baseEnd_6071332 : Nat := 3117511529023145119328459

theorem tailTrace_6071332 : CollatzResearch.WordTrace tailWord_6071332 prefixEnd_6071332 3117511529023145119328459 := by
  unfold tailWord_6071332
  simp only [CollatzResearch.WordTrace]
  refine ⟨110719835020304269899404125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147626446693739026532538833 110719835020304269899404125)
  ·
    refine ⟨41519938132614101212276547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110719835020304269899404125 41519938132614101212276547)
    ·
      refine ⟨62279907198921151818414821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41519938132614101212276547 62279907198921151818414821)
      ·
        refine ⟨11677482599797715965952779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62279907198921151818414821 11677482599797715965952779)
        ·
          refine ⟨17516223899696573948929169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11677482599797715965952779 17516223899696573948929169)
          ·
            refine ⟨13137167924772430461696877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17516223899696573948929169 13137167924772430461696877)
            ·
              refine ⟨4926437971789661423136329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13137167924772430461696877 4926437971789661423136329)
              ·
                refine ⟨3694828478842246067352247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4926437971789661423136329 3694828478842246067352247)
                ·
                  refine ⟨5542242718263369101028371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694828478842246067352247 5542242718263369101028371)
                  ·
                    refine ⟨8313364077395053651542557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5542242718263369101028371 8313364077395053651542557)
                    ·
                      refine ⟨3117511529023145119328459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8313364077395053651542557 3117511529023145119328459)
                      ·
                        rfl

theorem cell23_6071332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6071332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071332 prefixEnd_6071332 := by exact prefixLift 6071332
  have htrace : WordTrace (prefixWord ++ tailWord_6071332) baseStart_6071332 baseEnd_6071332 := by
    simpa [prefixWord, tailWord_6071332, baseEnd_6071332] using wordTrace_append hprefix tailTrace_6071332
  have hstable : (prefixWord ++ tailWord_6071332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071332).length < 2 ^ (prefixWord ++ tailWord_6071332).sum := by decide
  have hdescent : baseEnd_6071332 < baseStart_6071332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071347 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6]
def baseStart_6071347 : Nat := 118140960795 + 6071347 * 2 ^ 59
def prefixEnd_6071347 : Nat := 4983230072969 + 3 ^ 40 * 6071347 * 2
def baseEnd_6071347 : Nat := 3117519231232962560640889

theorem tailTrace_6071347 : CollatzResearch.WordTrace tailWord_6071347 prefixEnd_6071347 3117519231232962560640889 := by
  unfold tailWord_6071347
  simp only [CollatzResearch.WordTrace]
  refine ⟨221440217135554197360604295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147626811423702798240402863 221440217135554197360604295)
  ·
    refine ⟨332160325703331296040906443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221440217135554197360604295 332160325703331296040906443)
    ·
      refine ⟨498240488554996944061359665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332160325703331296040906443 498240488554996944061359665)
      ·
        refine ⟨373680366416247708046019749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498240488554996944061359665 373680366416247708046019749)
        ·
          refine ⟨70065068703046445258628703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 373680366416247708046019749 70065068703046445258628703)
          ·
            refine ⟨105097603054569667887943055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70065068703046445258628703 105097603054569667887943055)
            ·
              refine ⟨157646404581854501831914583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105097603054569667887943055 157646404581854501831914583)
              ·
                refine ⟨236469606872781752747871875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157646404581854501831914583 236469606872781752747871875)
                ·
                  refine ⟨354704410309172629121807813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236469606872781752747871875 354704410309172629121807813)
                  ·
                    refine ⟨66507076932969867960338965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 354704410309172629121807813 66507076932969867960338965)
                    ·
                      refine ⟨3117519231232962560640889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66507076932969867960338965 3117519231232962560640889)
                      ·
                        rfl

theorem cell23_6071347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_6071347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071347 prefixEnd_6071347 := by exact prefixLift 6071347
  have htrace : WordTrace (prefixWord ++ tailWord_6071347) baseStart_6071347 baseEnd_6071347 := by
    simpa [prefixWord, tailWord_6071347, baseEnd_6071347] using wordTrace_append hprefix tailTrace_6071347
  have hstable : (prefixWord ++ tailWord_6071347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071347).length < 2 ^ (prefixWord ++ tailWord_6071347).sum := by decide
  have hdescent : baseEnd_6071347 < baseStart_6071347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071358 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6071358 : Nat := 118140960795 + 6071358 * 2 ^ 59
def prefixEnd_6071358 : Nat := 4983230072969 + 3 ^ 40 * 6071358 * 2
def baseEnd_6071358 : Nat := 3117524879520162017603339

theorem tailTrace_6071358 : CollatzResearch.WordTrace tailWord_6071358 prefixEnd_6071358 3117524879520162017603339 := by
  unfold tailWord_6071358
  simp only [CollatzResearch.WordTrace]
  refine ⟨27680077292314293279906841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147627078892342897492836485 27680077292314293279906841)
  ·
    refine ⟨20760057969235719959930131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27680077292314293279906841 20760057969235719959930131)
    ·
      refine ⟨31140086953853579939895197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20760057969235719959930131 31140086953853579939895197)
      ·
        refine ⟨11677532607695092477460699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31140086953853579939895197 11677532607695092477460699)
        ·
          refine ⟨17516298911542638716191049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11677532607695092477460699 17516298911542638716191049)
          ·
            refine ⟨13137224183656979037143287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17516298911542638716191049 13137224183656979037143287)
            ·
              refine ⟨19705836275485468555714931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13137224183656979037143287 19705836275485468555714931)
              ·
                refine ⟨29558754413228202833572397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19705836275485468555714931 29558754413228202833572397)
                ·
                  refine ⟨11084532904960576062589649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29558754413228202833572397 11084532904960576062589649)
                  ·
                    refine ⟨8313399678720432046942237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11084532904960576062589649 8313399678720432046942237)
                    ·
                      refine ⟨3117524879520162017603339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8313399678720432046942237 3117524879520162017603339)
                      ·
                        rfl

theorem cell23_6071358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6071358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071358 prefixEnd_6071358 := by exact prefixLift 6071358
  have htrace : WordTrace (prefixWord ++ tailWord_6071358) baseStart_6071358 baseEnd_6071358 := by
    simpa [prefixWord, tailWord_6071358, baseEnd_6071358] using wordTrace_append hprefix tailTrace_6071358
  have hstable : (prefixWord ++ tailWord_6071358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071358).length < 2 ^ (prefixWord ++ tailWord_6071358).sum := by decide
  have hdescent : baseEnd_6071358 < baseStart_6071358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071382 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_6071382 : Nat := 118140960795 + 6071382 * 2 ^ 59
def prefixEnd_6071382 : Nat := 4983230072969 + 3 ^ 40 * 6071382 * 2
def baseEnd_6071382 : Nat := 1039179067685289974567743

theorem tailTrace_6071382 : CollatzResearch.WordTrace tailWord_6071382 prefixEnd_6071382 1039179067685289974567743 := by
  unfold tailWord_6071382
  simp only [CollatzResearch.WordTrace]
  refine ⟨13840093355651712396133025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147627662460284932225418933 13840093355651712396133025)
  ·
    refine ⟨10380070016738784297099769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13840093355651712396133025 10380070016738784297099769)
    ·
      refine ⟨7785052512554088222824827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10380070016738784297099769 7785052512554088222824827)
      ·
        refine ⟨11677578768831132334237241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785052512554088222824827 11677578768831132334237241)
        ·
          refine ⟨8758184076623349250677931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11677578768831132334237241 8758184076623349250677931)
          ·
            refine ⟨13137276114935023876016897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758184076623349250677931 13137276114935023876016897)
            ·
              refine ⟨9852957086201267907012673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13137276114935023876016897 9852957086201267907012673)
              ·
                refine ⟨7389717814650950930259505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9852957086201267907012673 7389717814650950930259505)
                ·
                  refine ⟨5542288360988213197694629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7389717814650950930259505 5542288360988213197694629)
                  ·
                    refine ⟨1039179067685289974567743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5542288360988213197694629 1039179067685289974567743)
                    ·
                      rfl

theorem cell23_6071382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_6071382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071382 prefixEnd_6071382 := by exact prefixLift 6071382
  have htrace : WordTrace (prefixWord ++ tailWord_6071382) baseStart_6071382 baseEnd_6071382 := by
    simpa [prefixWord, tailWord_6071382, baseEnd_6071382] using wordTrace_append hprefix tailTrace_6071382
  have hstable : (prefixWord ++ tailWord_6071382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071382).length < 2 ^ (prefixWord ++ tailWord_6071382).sum := by decide
  have hdescent : baseEnd_6071382 < baseStart_6071382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071389 : List Nat := [1, 4, 4, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_6071389 : Nat := 118140960795 + 6071389 * 2 ^ 59
def prefixEnd_6071389 : Nat := 4983230072969 + 3 ^ 40 * 6071389 * 2
def baseEnd_6071389 : Nat := 3117540797420451396315697

theorem tailTrace_6071389 : CollatzResearch.WordTrace tailWord_6071389 prefixEnd_6071389 3117540797420451396315697 := by
  unfold tailWord_6071389
  simp only [CollatzResearch.WordTrace]
  refine ⟨221441749001402038533633221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147627832667601359022422147 221441749001402038533633221)
  ·
    refine ⟨41520327937762882225056229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221441749001402038533633221 41520327937762882225056229)
    ·
      refine ⟨7785061488330540417198043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41520327937762882225056229 7785061488330540417198043)
      ·
        refine ⟨11677592232495810625797065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785061488330540417198043 11677592232495810625797065)
        ·
          refine ⟨8758194174371857969347799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11677592232495810625797065 8758194174371857969347799)
          ·
            refine ⟨13137291261557786954021699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758194174371857969347799 13137291261557786954021699)
            ·
              refine ⟨19705936892336680431032549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13137291261557786954021699 19705936892336680431032549)
              ·
                refine ⟨3694863167313127580818603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19705936892336680431032549 3694863167313127580818603)
                ·
                  refine ⟨5542294750969691371227905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694863167313127580818603 5542294750969691371227905)
                  ·
                    refine ⟨4156721063227268528420929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5542294750969691371227905 4156721063227268528420929)
                    ·
                      refine ⟨3117540797420451396315697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156721063227268528420929 3117540797420451396315697)
                      ·
                        rfl

theorem cell23_6071389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_6071389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071389 prefixEnd_6071389 := by exact prefixLift 6071389
  have htrace : WordTrace (prefixWord ++ tailWord_6071389) baseStart_6071389 baseEnd_6071389 := by
    simpa [prefixWord, tailWord_6071389, baseEnd_6071389] using wordTrace_append hprefix tailTrace_6071389
  have hstable : (prefixWord ++ tailWord_6071389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071389).length < 2 ^ (prefixWord ++ tailWord_6071389).sum := by decide
  have hdescent : baseEnd_6071389 < baseStart_6071389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071404 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_6071404 : Nat := 118140960795 + 6071404 * 2 ^ 59
def prefixEnd_6071404 : Nat := 4983230072969 + 3 ^ 40 * 6071404 * 2
def baseEnd_6071404 : Nat := 1039182833210089612542709

theorem tailTrace_6071404 : CollatzResearch.WordTrace tailWord_6071404 prefixEnd_6071404 1039182833210089612542709 := by
  unfold tailWord_6071404
  simp only [CollatzResearch.WordTrace]
  refine ⟨110721148048173848047714633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147628197397565130730286177 110721148048173848047714633)
  ·
    refine ⟨83040861036130386035785975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110721148048173848047714633 83040861036130386035785975)
    ·
      refine ⟨124561291554195579053678963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83040861036130386035785975 124561291554195579053678963)
      ·
        refine ⟨186841937331293368580518445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124561291554195579053678963 186841937331293368580518445)
        ·
          refine ⟨70065726499235013217694417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186841937331293368580518445 70065726499235013217694417)
          ·
            refine ⟨52549294874426259913270813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70065726499235013217694417 52549294874426259913270813)
            ·
              refine ⟨19705985577909847467476555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52549294874426259913270813 19705985577909847467476555)
              ·
                refine ⟨29558978366864771201214833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19705985577909847467476555 29558978366864771201214833)
                ·
                  refine ⟨22169233775148578400911125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29558978366864771201214833 22169233775148578400911125)
                  ·
                    refine ⟨1039182833210089612542709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22169233775148578400911125 1039182833210089612542709)
                    ·
                      rfl

theorem cell23_6071404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_6071404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071404 prefixEnd_6071404 := by exact prefixLift 6071404
  have htrace : WordTrace (prefixWord ++ tailWord_6071404) baseStart_6071404 baseEnd_6071404 := by
    simpa [prefixWord, tailWord_6071404, baseEnd_6071404] using wordTrace_append hprefix tailTrace_6071404
  have hstable : (prefixWord ++ tailWord_6071404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071404).length < 2 ^ (prefixWord ++ tailWord_6071404).sum := by decide
  have hdescent : baseEnd_6071404 < baseStart_6071404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071428 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_6071428 : Nat := 118140960795 + 6071428 * 2 ^ 59
def prefixEnd_6071428 : Nat := 4983230072969 + 3 ^ 40 * 6071428 * 2
def baseEnd_6071428 : Nat := 3117560823165976743728017

theorem tailTrace_6071428 : CollatzResearch.WordTrace tailWord_6071428 prefixEnd_6071428 3117560823165976743728017 := by
  unfold tailWord_6071428
  simp only [CollatzResearch.WordTrace]
  refine ⟨110721585724130374097151469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147628780965507165462868625 110721585724130374097151469)
  ·
    refine ⟨41520594646548890286431801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110721585724130374097151469 41520594646548890286431801)
    ·
      refine ⟨31140445984911667714823851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41520594646548890286431801 31140445984911667714823851)
      ·
        refine ⟨46710668977367501572235777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31140445984911667714823851 46710668977367501572235777)
        ·
          refine ⟨35033001733025626179176833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46710668977367501572235777 35033001733025626179176833)
          ·
            refine ⟨26274751299769219634382625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35033001733025626179176833 26274751299769219634382625)
            ·
              refine ⟨19706063474826914725786969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26274751299769219634382625 19706063474826914725786969)
              ·
                refine ⟨14779547606120186044340227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19706063474826914725786969 14779547606120186044340227)
                ·
                  refine ⟨22169321409180279066510341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14779547606120186044340227 22169321409180279066510341)
                  ·
                    refine ⟨4156747764221302324970689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22169321409180279066510341 4156747764221302324970689)
                    ·
                      refine ⟨3117560823165976743728017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156747764221302324970689 3117560823165976743728017)
                      ·
                        rfl

theorem cell23_6071428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_6071428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071428 prefixEnd_6071428 := by exact prefixLift 6071428
  have htrace : WordTrace (prefixWord ++ tailWord_6071428) baseStart_6071428 baseEnd_6071428 := by
    simpa [prefixWord, tailWord_6071428, baseEnd_6071428] using wordTrace_append hprefix tailTrace_6071428
  have hstable : (prefixWord ++ tailWord_6071428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071428).length < 2 ^ (prefixWord ++ tailWord_6071428).sum := by decide
  have hdescent : baseEnd_6071428 < baseStart_6071428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071434 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 9]
def baseStart_6071434 : Nat := 118140960795 + 6071434 * 2 ^ 59
def prefixEnd_6071434 : Nat := 4983230072969 + 3 ^ 40 * 6071434 * 2
def baseEnd_6071434 : Nat := 346395989338878191139221

theorem tailTrace_6071434 : CollatzResearch.WordTrace tailWord_6071434 prefixEnd_6071434 346395989338878191139221 := by
  unfold tailWord_6071434
  simp only [CollatzResearch.WordTrace]
  refine ⟨55360847571559752804755339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147628926857492674146014237 55360847571559752804755339)
  ·
    refine ⟨83041271357339629207133009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55360847571559752804755339 83041271357339629207133009)
    ·
      refine ⟨62280953518004721905349757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83041271357339629207133009 62280953518004721905349757)
      ·
        refine ⟨23355357569251770714506159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62280953518004721905349757 23355357569251770714506159)
        ·
          refine ⟨35033036353877656071759239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23355357569251770714506159 35033036353877656071759239)
          ·
            refine ⟨52549554530816484107638859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35033036353877656071759239 52549554530816484107638859)
            ·
              refine ⟨78824331796224726161458289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52549554530816484107638859 78824331796224726161458289)
              ·
                refine ⟨59118248847168544621093717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78824331796224726161458289 59118248847168544621093717)
                ·
                  refine ⟨346395989338878191139221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59118248847168544621093717 346395989338878191139221)
                  ·
                    rfl

theorem cell23_6071434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_6071434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071434 prefixEnd_6071434 := by exact prefixLift 6071434
  have htrace : WordTrace (prefixWord ++ tailWord_6071434) baseStart_6071434 baseEnd_6071434 := by
    simpa [prefixWord, tailWord_6071434, baseEnd_6071434] using wordTrace_append hprefix tailTrace_6071434
  have hstable : (prefixWord ++ tailWord_6071434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071434).length < 2 ^ (prefixWord ++ tailWord_6071434).sum := by decide
  have hdescent : baseEnd_6071434 < baseStart_6071434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071461 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_6071461 : Nat := 118140960795 + 6071461 * 2 ^ 59
def prefixEnd_6071461 : Nat := 4983230072969 + 3 ^ 40 * 6071461 * 2
def baseEnd_6071461 : Nat := 3117577768027575114615365

theorem tailTrace_6071461 : CollatzResearch.WordTrace tailWord_6071461 prefixEnd_6071461 3117577768027575114615365 := by
  unfold tailWord_6071461
  simp only [CollatzResearch.WordTrace]
  refine ⟨221444375057141194830254237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147629583371427463220169491 221444375057141194830254237)
  ·
    refine ⟨83041640646427948061345339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221444375057141194830254237 83041640646427948061345339)
    ·
      refine ⟨124562460969641922092018009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83041640646427948061345339 124562460969641922092018009)
      ·
        refine ⟨93421845727231441569013507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124562460969641922092018009 93421845727231441569013507)
        ·
          refine ⟨140132768590847162353520261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93421845727231441569013507 140132768590847162353520261)
          ·
            refine ⟨26274894110783842941285049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140132768590847162353520261 26274894110783842941285049)
            ·
              refine ⟨19706170583087882205963787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26274894110783842941285049 19706170583087882205963787)
              ·
                refine ⟨29559255874631823308945681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19706170583087882205963787 29559255874631823308945681)
                ·
                  refine ⟨22169441905973867481709261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29559255874631823308945681 22169441905973867481709261)
                  ·
                    refine ⟨8313540714740200305640973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22169441905973867481709261 8313540714740200305640973)
                    ·
                      refine ⟨3117577768027575114615365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8313540714740200305640973 3117577768027575114615365)
                      ·
                        rfl

theorem cell23_6071461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_6071461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071461 prefixEnd_6071461 := by exact prefixLift 6071461
  have htrace : WordTrace (prefixWord ++ tailWord_6071461) baseStart_6071461 baseEnd_6071461 := by
    simpa [prefixWord, tailWord_6071461, baseEnd_6071461] using wordTrace_append hprefix tailTrace_6071461
  have hstable : (prefixWord ++ tailWord_6071461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071461).length < 2 ^ (prefixWord ++ tailWord_6071461).sum := by decide
  have hdescent : baseEnd_6071461 < baseStart_6071461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071471 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 2, 5, 2]
def baseStart_6071471 : Nat := 118140960795 + 6071471 * 2 ^ 59
def prefixEnd_6071471 : Nat := 4983230072969 + 3 ^ 40 * 6071471 * 2
def baseEnd_6071471 : Nat := 3117582902834120075490319

theorem tailTrace_6071471 : CollatzResearch.WordTrace tailWord_6071471 prefixEnd_6071471 3117582902834120075490319 := by
  unfold tailWord_6071471
  simp only [CollatzResearch.WordTrace]
  refine ⟨221444739787104966538118267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147629826524736644358745511 221444739787104966538118267)
  ·
    refine ⟨332167109680657449807177401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221444739787104966538118267 332167109680657449807177401)
    ·
      refine ⟨249125332260493087355383051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332167109680657449807177401 249125332260493087355383051)
      ·
        refine ⟨373687998390739631033074577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249125332260493087355383051 373687998390739631033074577)
        ·
          refine ⟨280265998793054723274805933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373687998390739631033074577 280265998793054723274805933)
          ·
            refine ⟨105099749547395521228052225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280265998793054723274805933 105099749547395521228052225)
            ·
              refine ⟨78824812160546640921039169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105099749547395521228052225 78824812160546640921039169)
              ·
                refine ⟨59118609120409980690779377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78824812160546640921039169 59118609120409980690779377)
                ·
                  refine ⟨44338956840307485518084533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59118609120409980690779377 44338956840307485518084533)
                  ·
                    refine ⟨4156777203778826767320425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44338956840307485518084533 4156777203778826767320425)
                    ·
                      refine ⟨3117582902834120075490319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156777203778826767320425 3117582902834120075490319)
                      ·
                        rfl

theorem cell23_6071471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5, 2].length) (baseStart_6071471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071471 prefixEnd_6071471 := by exact prefixLift 6071471
  have htrace : WordTrace (prefixWord ++ tailWord_6071471) baseStart_6071471 baseEnd_6071471 := by
    simpa [prefixWord, tailWord_6071471, baseEnd_6071471] using wordTrace_append hprefix tailTrace_6071471
  have hstable : (prefixWord ++ tailWord_6071471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071471).length < 2 ^ (prefixWord ++ tailWord_6071471).sum := by decide
  have hdescent : baseEnd_6071471 < baseStart_6071471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071544 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_6071544 : Nat := 118140960795 + 6071544 * 2 ^ 59
def prefixEnd_6071544 : Nat := 4983230072969 + 3 ^ 40 * 6071544 * 2
def baseEnd_6071544 : Nat := 3117620386921898289877483

theorem tailTrace_6071544 : CollatzResearch.WordTrace tailWord_6071544 prefixEnd_6071544 3117620386921898289877483 := by
  unfold tailWord_6071544
  simp only [CollatzResearch.WordTrace]
  refine ⟨110723701157920250002762843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147631601543893666670350457 110723701157920250002762843)
  ·
    refine ⟨166085551736880375004144265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110723701157920250002762843 166085551736880375004144265)
    ·
      refine ⟨124564163802660281253108199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166085551736880375004144265 124564163802660281253108199)
      ·
        refine ⟨186846245703990421879662299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124564163802660281253108199 186846245703990421879662299)
        ·
          refine ⟨280269368555985632819493449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186846245703990421879662299 280269368555985632819493449)
          ·
            refine ⟨210202026416989224614620087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280269368555985632819493449 210202026416989224614620087)
            ·
              refine ⟨315303039625483836921930131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210202026416989224614620087 315303039625483836921930131)
              ·
                refine ⟨472954559438225755382895197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315303039625483836921930131 472954559438225755382895197)
                ·
                  refine ⟨177357959789334658268585699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472954559438225755382895197 177357959789334658268585699)
                  ·
                    refine ⟨266036939684001987402878549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177357959789334658268585699 266036939684001987402878549)
                    ·
                      refine ⟨3117620386921898289877483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 266036939684001987402878549 3117620386921898289877483)
                      ·
                        rfl

theorem cell23_6071544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_6071544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071544 prefixEnd_6071544 := by exact prefixLift 6071544
  have htrace : WordTrace (prefixWord ++ tailWord_6071544) baseStart_6071544 baseEnd_6071544 := by
    simpa [prefixWord, tailWord_6071544, baseEnd_6071544] using wordTrace_append hprefix tailTrace_6071544
  have hstable : (prefixWord ++ tailWord_6071544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071544).length < 2 ^ (prefixWord ++ tailWord_6071544).sum := by decide
  have hdescent : baseEnd_6071544 < baseStart_6071544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071588 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_6071588 : Nat := 118140960795 + 6071588 * 2 ^ 59
def prefixEnd_6071588 : Nat := 4983230072969 + 3 ^ 40 * 6071588 * 2
def baseEnd_6071588 : Nat := 1039214326690232039242427

theorem tailTrace_6071588 : CollatzResearch.WordTrace tailWord_6071588 prefixEnd_6071588 1039214326690232039242427 := by
  unfold tailWord_6071588
  simp only [CollatzResearch.WordTrace]
  refine ⟨110724503563840547760063709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147632671418454063680084945 110724503563840547760063709)
  ·
    refine ⟨41521688836440205410023891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110724503563840547760063709 41521688836440205410023891)
    ·
      refine ⟨62282533254660308115035837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41521688836440205410023891 62282533254660308115035837)
      ·
        refine ⟨23355949970497615543138439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62282533254660308115035837 23355949970497615543138439)
        ·
          refine ⟨35033924955746423314707659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23355949970497615543138439 35033924955746423314707659)
          ·
            refine ⟨52550887433619634972061489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35033924955746423314707659 52550887433619634972061489)
            ·
              refine ⟨39413165575214726229046117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52550887433619634972061489 39413165575214726229046117)
              ·
                refine ⟨7389968545352761167946147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39413165575214726229046117 7389968545352761167946147)
                ·
                  refine ⟨11084952818029141751919221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7389968545352761167946147 11084952818029141751919221)
                  ·
                    refine ⟨1039214326690232039242427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11084952818029141751919221 1039214326690232039242427)
                    ·
                      rfl

theorem cell23_6071588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_6071588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071588 prefixEnd_6071588 := by exact prefixLift 6071588
  have htrace : WordTrace (prefixWord ++ tailWord_6071588) baseStart_6071588 baseEnd_6071588 := by
    simpa [prefixWord, tailWord_6071588, baseEnd_6071588] using wordTrace_append hprefix tailTrace_6071588
  have hstable : (prefixWord ++ tailWord_6071588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071588).length < 2 ^ (prefixWord ++ tailWord_6071588).sum := by decide
  have hdescent : baseEnd_6071588 < baseStart_6071588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071602 : List Nat := [3, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_6071602 : Nat := 118140960795 + 6071602 * 2 ^ 59
def prefixEnd_6071602 : Nat := 4983230072969 + 3 ^ 40 * 6071602 * 2
def baseEnd_6071602 : Nat := 3117650168799859062952217

theorem tailTrace_6071602 : CollatzResearch.WordTrace tailWord_6071602 prefixEnd_6071602 3117650168799859062952217 := by
  unfold tailWord_6071602
  simp only [CollatzResearch.WordTrace]
  refine ⟨55362379437407593977784265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147633011833086917274091373 55362379437407593977784265)
  ·
    refine ⟨41521784578055695483338199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55362379437407593977784265 41521784578055695483338199)
    ·
      refine ⟨62282676867083543225007299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41521784578055695483338199 62282676867083543225007299)
      ·
        refine ⟨93424015300625314837510949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62282676867083543225007299 93424015300625314837510949)
        ·
          refine ⟨17517002868867246532033303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93424015300625314837510949 17517002868867246532033303)
          ·
            refine ⟨26275504303300869798049955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17517002868867246532033303 26275504303300869798049955)
            ·
              refine ⟨39413256454951304697074933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26275504303300869798049955 39413256454951304697074933)
              ·
                refine ⟨3694992792651684815350775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39413256454951304697074933 3694992792651684815350775)
                ·
                  refine ⟨5542489188977527223026163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694992792651684815350775 5542489188977527223026163)
                  ·
                    refine ⟨8313733783466290834539245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5542489188977527223026163 8313733783466290834539245)
                    ·
                      refine ⟨3117650168799859062952217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8313733783466290834539245 3117650168799859062952217)
                      ·
                        rfl

theorem cell23_6071602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_6071602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071602 prefixEnd_6071602 := by exact prefixLift 6071602
  have htrace : WordTrace (prefixWord ++ tailWord_6071602) baseStart_6071602 baseEnd_6071602 := by
    simpa [prefixWord, tailWord_6071602, baseEnd_6071602] using wordTrace_append hprefix tailTrace_6071602
  have hstable : (prefixWord ++ tailWord_6071602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071602).length < 2 ^ (prefixWord ++ tailWord_6071602).sum := by decide
  have hdescent : baseEnd_6071602 < baseStart_6071602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071605 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_6071605 : Nat := 118140960795 + 6071605 * 2 ^ 59
def prefixEnd_6071605 : Nat := 4983230072969 + 3 ^ 40 * 6071605 * 2
def baseEnd_6071605 : Nat := 1039217236413940850404901

theorem tailTrace_6071605 : CollatzResearch.WordTrace tailWord_6071605 prefixEnd_6071605 1039217236413940850404901 := by
  unfold tailWord_6071605
  simp only [CollatzResearch.WordTrace]
  refine ⟨221449627168619507423496269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147633084779079671615664179 221449627168619507423496269)
  ·
    refine ⟨83043610188232315283811101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221449627168619507423496269 83043610188232315283811101)
    ·
      refine ⟨31141353820587118231429163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83043610188232315283811101 31141353820587118231429163)
      ·
        refine ⟨46712030730880677347143745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31141353820587118231429163 46712030730880677347143745)
        ·
          refine ⟨35034023048160508010357809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46712030730880677347143745 35034023048160508010357809)
          ·
            refine ⟨26275517286120381007768357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35034023048160508010357809 26275517286120381007768357)
            ·
              refine ⟨4926659491147571438956567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26275517286120381007768357 4926659491147571438956567)
              ·
                refine ⟨7389989236721357158434851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926659491147571438956567 7389989236721357158434851)
                ·
                  refine ⟨11084983855082035737652277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7389989236721357158434851 11084983855082035737652277)
                  ·
                    refine ⟨1039217236413940850404901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11084983855082035737652277 1039217236413940850404901)
                    ·
                      rfl

theorem cell23_6071605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_6071605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071605 prefixEnd_6071605 := by exact prefixLift 6071605
  have htrace : WordTrace (prefixWord ++ tailWord_6071605) baseStart_6071605 baseEnd_6071605 := by
    simpa [prefixWord, tailWord_6071605, baseEnd_6071605] using wordTrace_append hprefix tailTrace_6071605
  have hstable : (prefixWord ++ tailWord_6071605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071605).length < 2 ^ (prefixWord ++ tailWord_6071605).sum := by decide
  have hdescent : baseEnd_6071605 < baseStart_6071605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071621 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_6071621 : Nat := 118140960795 + 6071621 * 2 ^ 59
def prefixEnd_6071621 : Nat := 4983230072969 + 3 ^ 40 * 6071621 * 2
def baseEnd_6071621 : Nat := 3117659924932294488614629

theorem tailTrace_6071621 : CollatzResearch.WordTrace tailWord_6071621 prefixEnd_6071621 3117659924932294488614629 := by
  unfold tailWord_6071621
  simp only [CollatzResearch.WordTrace]
  refine ⟨221450210736561542156078717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147633473824374361437385811 221450210736561542156078717)
  ·
    refine ⟨83043829026210578308529519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221450210736561542156078717 83043829026210578308529519)
    ·
      refine ⟨124565743539315867462794279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83043829026210578308529519 124565743539315867462794279)
      ·
        refine ⟨186848615308973801194191419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124565743539315867462794279 186848615308973801194191419)
        ·
          refine ⟨280272922963460701791287129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186848615308973801194191419 280272922963460701791287129)
          ·
            refine ⟨210204692222595526343465347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280272922963460701791287129 210204692222595526343465347)
            ·
              refine ⟨315307038333893289515198021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210204692222595526343465347 315307038333893289515198021)
              ·
                refine ⟨59120069687604991784099629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315307038333893289515198021 59120069687604991784099629)
                ·
                  refine ⟨22170026132851871919037361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59120069687604991784099629 22170026132851871919037361)
                  ·
                    refine ⟨16627519599638903939278021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22170026132851871919037361 16627519599638903939278021)
                    ·
                      refine ⟨3117659924932294488614629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16627519599638903939278021 3117659924932294488614629)
                      ·
                        rfl

theorem cell23_6071621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_6071621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071621 prefixEnd_6071621 := by exact prefixLift 6071621
  have htrace : WordTrace (prefixWord ++ tailWord_6071621) baseStart_6071621 baseEnd_6071621 := by
    simpa [prefixWord, tailWord_6071621, baseEnd_6071621] using wordTrace_append hprefix tailTrace_6071621
  have hstable : (prefixWord ++ tailWord_6071621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071621).length < 2 ^ (prefixWord ++ tailWord_6071621).sum := by decide
  have hdescent : baseEnd_6071621 < baseStart_6071621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071625 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 3, 2, 2]
def baseStart_6071625 : Nat := 118140960795 + 6071625 * 2 ^ 59
def prefixEnd_6071625 : Nat := 4983230072969 + 3 ^ 40 * 6071625 * 2
def baseEnd_6071625 : Nat := 3117661978854912472964611

theorem tailTrace_6071625 : CollatzResearch.WordTrace tailWord_6071625 prefixEnd_6071625 3117661978854912472964611 := by
  unfold tailWord_6071625
  simp only [CollatzResearch.WordTrace]
  refine ⟨221450356628547050839224329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147633571085698033892816219 221450356628547050839224329)
  ·
    refine ⟨166087767471410288129418247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221450356628547050839224329 166087767471410288129418247)
    ·
      refine ⟨249131651207115432194127371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166087767471410288129418247 249131651207115432194127371)
      ·
        refine ⟨373697476810673148291191057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249131651207115432194127371 373697476810673148291191057)
        ·
          refine ⟨280273107608004861218393293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373697476810673148291191057 280273107608004861218393293)
          ·
            refine ⟨105102415353001822956897485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280273107608004861218393293 105102415353001822956897485)
            ·
              refine ⟨39413405757375683608836557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105102415353001822956897485 39413405757375683608836557)
              ·
                refine ⟨14780027159015881353313709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39413405757375683608836557 14780027159015881353313709)
                ·
                  refine ⟨5542510184630955507492641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14780027159015881353313709 5542510184630955507492641)
                  ·
                    refine ⟨4156882638473216630619481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5542510184630955507492641 4156882638473216630619481)
                    ·
                      refine ⟨3117661978854912472964611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156882638473216630619481 3117661978854912472964611)
                      ·
                        rfl

theorem cell23_6071625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 2, 2].length) (baseStart_6071625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071625 prefixEnd_6071625 := by exact prefixLift 6071625
  have htrace : WordTrace (prefixWord ++ tailWord_6071625) baseStart_6071625 baseEnd_6071625 := by
    simpa [prefixWord, tailWord_6071625, baseEnd_6071625] using wordTrace_append hprefix tailTrace_6071625
  have hstable : (prefixWord ++ tailWord_6071625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071625).length < 2 ^ (prefixWord ++ tailWord_6071625).sum := by decide
  have hdescent : baseEnd_6071625 < baseStart_6071625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071628 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6071628 : Nat := 118140960795 + 6071628 * 2 ^ 59
def prefixEnd_6071628 : Nat := 4983230072969 + 3 ^ 40 * 6071628 * 2
def baseEnd_6071628 : Nat := 3117663519296875961227097

theorem tailTrace_6071628 : CollatzResearch.WordTrace tailWord_6071628 prefixEnd_6071628 3117663519296875961227097 := by
  unfold tailWord_6071628
  simp only [CollatzResearch.WordTrace]
  refine ⟨110725233023768091175791769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147633644031690788234389025 110725233023768091175791769)
  ·
    refine ⟨83043924767826068381843827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110725233023768091175791769 83043924767826068381843827)
    ·
      refine ⟨124565887151739102572765741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83043924767826068381843827 124565887151739102572765741)
      ·
        refine ⟨46712207681902163464787153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124565887151739102572765741 46712207681902163464787153)
        ·
          refine ⟨35034155761426622598590365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46712207681902163464787153 35034155761426622598590365)
          ·
            refine ⟨13137808410534983474471387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35034155761426622598590365 13137808410534983474471387)
            ·
              refine ⟨19706712615802475211707081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13137808410534983474471387 19706712615802475211707081)
              ·
                refine ⟨14780034461851856408780311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19706712615802475211707081 14780034461851856408780311)
                ·
                  refine ⟨22170051692777784613170467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14780034461851856408780311 22170051692777784613170467)
                  ·
                    refine ⟨33255077539166676919755701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22170051692777784613170467 33255077539166676919755701)
                    ·
                      refine ⟨3117663519296875961227097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33255077539166676919755701 3117663519296875961227097)
                      ·
                        rfl

theorem cell23_6071628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6071628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071628 prefixEnd_6071628 := by exact prefixLift 6071628
  have htrace : WordTrace (prefixWord ++ tailWord_6071628) baseStart_6071628 baseEnd_6071628 := by
    simpa [prefixWord, tailWord_6071628, baseEnd_6071628] using wordTrace_append hprefix tailTrace_6071628
  have hstable : (prefixWord ++ tailWord_6071628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071628).length < 2 ^ (prefixWord ++ tailWord_6071628).sum := by decide
  have hdescent : baseEnd_6071628 < baseStart_6071628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071635 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 2, 4]
def baseStart_6071635 : Nat := 118140960795 + 6071635 * 2 ^ 59
def prefixEnd_6071635 : Nat := 4983230072969 + 3 ^ 40 * 6071635 * 2
def baseEnd_6071635 : Nat := 1039222371220485811279855

theorem tailTrace_6071635 : CollatzResearch.WordTrace tailWord_6071635 prefixEnd_6071635 1039222371220485811279855 := by
  unfold tailWord_6071635
  simp only [CollatzResearch.WordTrace]
  refine ⟨221450721358510822547088359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147633814239007215031392239 221450721358510822547088359)
  ·
    refine ⟨332176082037766233820632539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221450721358510822547088359 332176082037766233820632539)
    ·
      refine ⟨498264123056649350730948809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332176082037766233820632539 498264123056649350730948809)
      ·
        refine ⟨373698092292487013048211607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498264123056649350730948809 373698092292487013048211607)
        ·
          refine ⟨560547138438730519572317411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373698092292487013048211607 560547138438730519572317411)
          ·
            refine ⟨840820707658095779358476117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560547138438730519572317411 840820707658095779358476117)
            ·
              refine ⟨4926683833934154957178571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 840820707658095779358476117 4926683833934154957178571)
              ·
                refine ⟨7390025750901232435767857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926683833934154957178571 7390025750901232435767857)
                ·
                  refine ⟨5542519313175924326825893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7390025750901232435767857 5542519313175924326825893)
                  ·
                    refine ⟨1039222371220485811279855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5542519313175924326825893 1039222371220485811279855)
                    ·
                      rfl

theorem cell23_6071635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 4].length) (baseStart_6071635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071635 prefixEnd_6071635 := by exact prefixLift 6071635
  have htrace : WordTrace (prefixWord ++ tailWord_6071635) baseStart_6071635 baseEnd_6071635 := by
    simpa [prefixWord, tailWord_6071635, baseEnd_6071635] using wordTrace_append hprefix tailTrace_6071635
  have hstable : (prefixWord ++ tailWord_6071635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071635).length < 2 ^ (prefixWord ++ tailWord_6071635).sum := by decide
  have hdescent : baseEnd_6071635 < baseStart_6071635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071648 : List Nat := [2, 1, 1, 3, 4, 1, 4, 7]
def baseStart_6071648 : Nat := 118140960795 + 6071648 * 2 ^ 59
def prefixEnd_6071648 : Nat := 4983230072969 + 3 ^ 40 * 6071648 * 2
def baseEnd_6071648 : Nat := 115469399589257995665815

theorem tailTrace_6071648 : CollatzResearch.WordTrace tailWord_6071648 prefixEnd_6071648 115469399589257995665815 := by
  unfold tailWord_6071648
  simp only [CollatzResearch.WordTrace]
  refine ⟨110725597753731862883655799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147634130338309150511541065 110725597753731862883655799)
  ·
    refine ⟨166088396630597794325483699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110725597753731862883655799 166088396630597794325483699)
    ·
      refine ⟨249132594945896691488225549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166088396630597794325483699 249132594945896691488225549)
      ·
        refine ⟨93424723104711259308084581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249132594945896691488225549 93424723104711259308084581)
        ·
          refine ⟨17517135582133361120265859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93424723104711259308084581 17517135582133361120265859)
          ·
            refine ⟨26275703373200041680398789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17517135582133361120265859 26275703373200041680398789)
            ·
              refine ⟨4926694382475007815074773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26275703373200041680398789 4926694382475007815074773)
              ·
                refine ⟨115469399589257995665815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4926694382475007815074773 115469399589257995665815)
                ·
                  rfl

theorem cell23_6071648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 7].length) (baseStart_6071648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071648 prefixEnd_6071648 := by exact prefixLift 6071648
  have htrace : WordTrace (prefixWord ++ tailWord_6071648) baseStart_6071648 baseEnd_6071648 := by
    simpa [prefixWord, tailWord_6071648, baseEnd_6071648] using wordTrace_append hprefix tailTrace_6071648
  have hstable : (prefixWord ++ tailWord_6071648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071648).length < 2 ^ (prefixWord ++ tailWord_6071648).sum := by decide
  have hdescent : baseEnd_6071648 < baseStart_6071648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071662 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6071662 : Nat := 118140960795 + 6071662 * 2 ^ 59
def prefixEnd_6071662 : Nat := 4983230072969 + 3 ^ 40 * 6071662 * 2
def baseEnd_6071662 : Nat := 3117680977639128828201941

theorem tailTrace_6071662 : CollatzResearch.WordTrace tailWord_6071662 prefixEnd_6071662 3117680977639128828201941 := by
  unfold tailWord_6071662
  simp only [CollatzResearch.WordTrace]
  refine ⟨27681463266176625769790155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147634470752942004105547493 27681463266176625769790155)
  ·
    refine ⟨41522194899264938654685233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27681463266176625769790155 41522194899264938654685233)
    ·
      refine ⟨31141646174448703991013925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41522194899264938654685233 31141646174448703991013925)
      ·
        refine ⟨5839058657709131998315111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31141646174448703991013925 5839058657709131998315111)
        ·
          refine ⟨8758587986563697997472667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5839058657709131998315111 8758587986563697997472667)
          ·
            refine ⟨13137881979845546996209001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758587986563697997472667 13137881979845546996209001)
            ·
              refine ⟨9853411484884160247156751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13137881979845546996209001 9853411484884160247156751)
              ·
                refine ⟨14780117227326240370735127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9853411484884160247156751 14780117227326240370735127)
                ·
                  refine ⟨22170175840989360556102691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14780117227326240370735127 22170175840989360556102691)
                  ·
                    refine ⟨33255263761484040834154037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22170175840989360556102691 33255263761484040834154037)
                    ·
                      refine ⟨3117680977639128828201941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33255263761484040834154037 3117680977639128828201941)
                      ·
                        rfl

theorem cell23_6071662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6071662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071662 prefixEnd_6071662 := by exact prefixLift 6071662
  have htrace : WordTrace (prefixWord ++ tailWord_6071662) baseStart_6071662 baseEnd_6071662 := by
    simpa [prefixWord, tailWord_6071662, baseEnd_6071662] using wordTrace_append hprefix tailTrace_6071662
  have hstable : (prefixWord ++ tailWord_6071662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071662).length < 2 ^ (prefixWord ++ tailWord_6071662).sum := by decide
  have hdescent : baseEnd_6071662 < baseStart_6071662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071671 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_6071671 : Nat := 118140960795 + 6071671 * 2 ^ 59
def prefixEnd_6071671 : Nat := 4983230072969 + 3 ^ 40 * 6071671 * 2
def baseEnd_6071671 : Nat := 3117685598965019292989399

theorem tailTrace_6071671 : CollatzResearch.WordTrace tailWord_6071671 prefixEnd_6071671 3117685598965019292989399 := by
  unfold tailWord_6071671
  simp only [CollatzResearch.WordTrace]
  refine ⟨221452034386380400695398867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147634689590920267130265911 221452034386380400695398867)
  ·
    refine ⟨332178051579570601043098301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221452034386380400695398867 332178051579570601043098301)
    ·
      refine ⟨124566769342338975391161863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332178051579570601043098301 124566769342338975391161863)
      ·
        refine ⟨186850154013508463086742795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124566769342338975391161863 186850154013508463086742795)
        ·
          refine ⟨280275231020262694630114193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186850154013508463086742795 280275231020262694630114193)
          ·
            refine ⟨210206423265197020972585645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280275231020262694630114193 210206423265197020972585645)
            ·
              refine ⟨78827408724448882864719617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210206423265197020972585645 78827408724448882864719617)
              ·
                refine ⟨59120556543336662148539713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78827408724448882864719617 59120556543336662148539713)
                ·
                  refine ⟨44340417407502496611404785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59120556543336662148539713 44340417407502496611404785)
                  ·
                    refine ⟨33255313055626872458553589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44340417407502496611404785 33255313055626872458553589)
                    ·
                      refine ⟨3117685598965019292989399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33255313055626872458553589 3117685598965019292989399)
                      ·
                        rfl

theorem cell23_6071671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_6071671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071671 prefixEnd_6071671 := by exact prefixLift 6071671
  have htrace : WordTrace (prefixWord ++ tailWord_6071671) baseStart_6071671 baseEnd_6071671 := by
    simpa [prefixWord, tailWord_6071671, baseEnd_6071671] using wordTrace_append hprefix tailTrace_6071671
  have hstable : (prefixWord ++ tailWord_6071671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071671).length < 2 ^ (prefixWord ++ tailWord_6071671).sum := by decide
  have hdescent : baseEnd_6071671 < baseStart_6071671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071675 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 3]
def baseStart_6071675 : Nat := 118140960795 + 6071675 * 2 ^ 59
def prefixEnd_6071675 : Nat := 4983230072969 + 3 ^ 40 * 6071675 * 2
def baseEnd_6071675 : Nat := 3117687652887637277339381

theorem tailTrace_6071675 : CollatzResearch.WordTrace tailWord_6071675 prefixEnd_6071675 3117687652887637277339381 := by
  unfold tailWord_6071675
  simp only [CollatzResearch.WordTrace]
  refine ⟨221452180278365909378544479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147634786852243939585696319 221452180278365909378544479)
  ·
    refine ⟨332178270417548864067816719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221452180278365909378544479 332178270417548864067816719)
    ·
      refine ⟨498267405626323296101725079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332178270417548864067816719 498267405626323296101725079)
      ·
        refine ⟨747401108439484944152587619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498267405626323296101725079 747401108439484944152587619)
        ·
          refine ⟨1121101662659227416228881429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747401108439484944152587619 1121101662659227416228881429)
          ·
            refine ⟨52551640437151285135728817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1121101662659227416228881429 52551640437151285135728817)
            ·
              refine ⟨39413730327863463851796613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52551640437151285135728817 39413730327863463851796613)
              ·
                refine ⟨7390074436474399472211865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39413730327863463851796613 7390074436474399472211865)
                ·
                  refine ⟨5542555827355799604158899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7390074436474399472211865 5542555827355799604158899)
                  ·
                    refine ⟨8313833741033699406238349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5542555827355799604158899 8313833741033699406238349)
                    ·
                      refine ⟨3117687652887637277339381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8313833741033699406238349 3117687652887637277339381)
                      ·
                        rfl

theorem cell23_6071675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 1, 3].length) (baseStart_6071675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071675 prefixEnd_6071675 := by exact prefixLift 6071675
  have htrace : WordTrace (prefixWord ++ tailWord_6071675) baseStart_6071675 baseEnd_6071675 := by
    simpa [prefixWord, tailWord_6071675, baseEnd_6071675] using wordTrace_append hprefix tailTrace_6071675
  have hstable : (prefixWord ++ tailWord_6071675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071675).length < 2 ^ (prefixWord ++ tailWord_6071675).sum := by decide
  have hdescent : baseEnd_6071675 < baseStart_6071675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071691 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 1, 8]
def baseStart_6071691 : Nat := 118140960795 + 6071691 * 2 ^ 59
def prefixEnd_6071691 : Nat := 4983230072969 + 3 ^ 40 * 6071691 * 2
def baseEnd_6071691 : Nat := 1039231956192703071579769

theorem tailTrace_6071691 : CollatzResearch.WordTrace tailWord_6071691 prefixEnd_6071691 1039231956192703071579769 := by
  unfold tailWord_6071691
  simp only [CollatzResearch.WordTrace]
  refine ⟨221452763846307944111126927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147635175897538629407417951 221452763846307944111126927)
  ·
    refine ⟨332179145769461916166690391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221452763846307944111126927 332179145769461916166690391)
    ·
      refine ⟨498268718654192874250035587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332179145769461916166690391 498268718654192874250035587)
      ·
        refine ⟨747403077981289311375053381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498268718654192874250035587 747403077981289311375053381)
        ·
          refine ⟨140138077121491745882822509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 747403077981289311375053381 140138077121491745882822509)
          ·
            refine ⟨52551778920559404706058441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140138077121491745882822509 52551778920559404706058441)
            ·
              refine ⟨39413834190419553529543831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52551778920559404706058441 39413834190419553529543831)
              ·
                refine ⟨59120751285629330294315747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39413834190419553529543831 59120751285629330294315747)
                ·
                  refine ⟨88681126928443995441473621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59120751285629330294315747 88681126928443995441473621)
                  ·
                    refine ⟨1039231956192703071579769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 88681126928443995441473621 1039231956192703071579769)
                    ·
                      rfl

theorem cell23_6071691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_6071691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071691 prefixEnd_6071691 := by exact prefixLift 6071691
  have htrace : WordTrace (prefixWord ++ tailWord_6071691) baseStart_6071691 baseEnd_6071691 := by
    simpa [prefixWord, tailWord_6071691, baseEnd_6071691] using wordTrace_append hprefix tailTrace_6071691
  have hstable : (prefixWord ++ tailWord_6071691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071691).length < 2 ^ (prefixWord ++ tailWord_6071691).sum := by decide
  have hdescent : baseEnd_6071691 < baseStart_6071691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071715 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 1, 4, 2]
def baseStart_6071715 : Nat := 118140960795 + 6071715 * 2 ^ 59
def prefixEnd_6071715 : Nat := 4983230072969 + 3 ^ 40 * 6071715 * 2
def baseEnd_6071715 : Nat := 3117708192113817120839197

theorem tailTrace_6071715 : CollatzResearch.WordTrace tailWord_6071715 prefixEnd_6071715 3117708192113817120839197 := by
  unfold tailWord_6071715
  simp only [CollatzResearch.WordTrace]
  refine ⟨221453639198220996210000599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147635759465480664140000399 221453639198220996210000599)
  ·
    refine ⟨332180458797331494315000899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221453639198220996210000599 332180458797331494315000899)
    ·
      refine ⟨498270688195997241472501349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332180458797331494315000899 498270688195997241472501349)
      ·
        refine ⟨93425754036749482776094003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 498270688195997241472501349 93425754036749482776094003)
        ·
          refine ⟨140138631055124224164141005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93425754036749482776094003 140138631055124224164141005)
          ·
            refine ⟨52551986645671584061552877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140138631055124224164141005 52551986645671584061552877)
            ·
              refine ⟨19706994992126844023082329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52551986645671584061552877 19706994992126844023082329)
              ·
                refine ⟨14780246244095133017311747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19706994992126844023082329 14780246244095133017311747)
                ·
                  refine ⟨22170369366142699525967621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14780246244095133017311747 22170369366142699525967621)
                  ·
                    refine ⟨4156944256151756161118929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22170369366142699525967621 4156944256151756161118929)
                    ·
                      refine ⟨3117708192113817120839197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156944256151756161118929 3117708192113817120839197)
                      ·
                        rfl

theorem cell23_6071715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_6071715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071715 prefixEnd_6071715 := by exact prefixLift 6071715
  have htrace : WordTrace (prefixWord ++ tailWord_6071715) baseStart_6071715 baseEnd_6071715 := by
    simpa [prefixWord, tailWord_6071715, baseEnd_6071715] using wordTrace_append hprefix tailTrace_6071715
  have hstable : (prefixWord ++ tailWord_6071715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071715).length < 2 ^ (prefixWord ++ tailWord_6071715).sum := by decide
  have hdescent : baseEnd_6071715 < baseStart_6071715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071719 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_6071719 : Nat := 118140960795 + 6071719 * 2 ^ 59
def prefixEnd_6071719 : Nat := 4983230072969 + 3 ^ 40 * 6071719 * 2
def baseEnd_6071719 : Nat := 3117710246036435105189179

theorem tailTrace_6071719 : CollatzResearch.WordTrace tailWord_6071719 prefixEnd_6071719 3117710246036435105189179 := by
  unfold tailWord_6071719
  simp only [CollatzResearch.WordTrace]
  refine ⟨221453785090206504893146211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147635856726804336595430807 221453785090206504893146211)
  ·
    refine ⟨332180677635309757339719317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221453785090206504893146211 332180677635309757339719317)
    ·
      refine ⟨15570969264155144875299343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 332180677635309757339719317 15570969264155144875299343)
      ·
        refine ⟨23356453896232717312949015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15570969264155144875299343 23356453896232717312949015)
        ·
          refine ⟨35034680844349075969423523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23356453896232717312949015 35034680844349075969423523)
          ·
            refine ⟨52552021266523613954135285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35034680844349075969423523 52552021266523613954135285)
            ·
              refine ⟨4926751993736588808200183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52552021266523613954135285 4926751993736588808200183)
              ·
                refine ⟨7390127990604883212300275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926751993736588808200183 7390127990604883212300275)
                ·
                  refine ⟨11085191985907324818450413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7390127990604883212300275 11085191985907324818450413)
                  ·
                    refine ⟨4156946994715246806918905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11085191985907324818450413 4156946994715246806918905)
                    ·
                      refine ⟨3117710246036435105189179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4156946994715246806918905 3117710246036435105189179)
                      ·
                        rfl

theorem cell23_6071719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_6071719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071719 prefixEnd_6071719 := by exact prefixLift 6071719
  have htrace : WordTrace (prefixWord ++ tailWord_6071719) baseStart_6071719 baseEnd_6071719 := by
    simpa [prefixWord, tailWord_6071719, baseEnd_6071719] using wordTrace_append hprefix tailTrace_6071719
  have hstable : (prefixWord ++ tailWord_6071719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071719).length < 2 ^ (prefixWord ++ tailWord_6071719).sum := by decide
  have hdescent : baseEnd_6071719 < baseStart_6071719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071731 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7]
def baseStart_6071731 : Nat := 118140960795 + 6071731 * 2 ^ 59
def prefixEnd_6071731 : Nat := 4983230072969 + 3 ^ 40 * 6071731 * 2
def baseEnd_6071731 : Nat := 3117716407804289058239123

theorem tailTrace_6071731 : CollatzResearch.WordTrace tailWord_6071731 prefixEnd_6071731 3117716407804289058239123 := by
  unfold tailWord_6071731
  simp only [CollatzResearch.WordTrace]
  refine ⟨221454222766163030942583047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147636148510775353961722031 221454222766163030942583047)
  ·
    refine ⟨332181334149244546413874571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221454222766163030942583047 332181334149244546413874571)
    ·
      refine ⟨498272001223866819620811857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332181334149244546413874571 498272001223866819620811857)
      ·
        refine ⟨373704000917900114715608893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498272001223866819620811857 373704000917900114715608893)
        ·
          refine ⟨140139000344212543018353335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373704000917900114715608893 140139000344212543018353335)
          ·
            refine ⟨210208500516318814527530003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140139000344212543018353335 210208500516318814527530003)
            ·
              refine ⟨315312750774478221791295005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210208500516318814527530003 315312750774478221791295005)
              ·
                refine ⟨118242281540429333171735627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315312750774478221791295005 118242281540429333171735627)
                ·
                  refine ⟨177363422310643999757603441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118242281540429333171735627 177363422310643999757603441)
                  ·
                    refine ⟨133022566732982999818202581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177363422310643999757603441 133022566732982999818202581)
                    ·
                      refine ⟨3117716407804289058239123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133022566732982999818202581 3117716407804289058239123)
                      ·
                        rfl

theorem cell23_6071731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_6071731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071731 prefixEnd_6071731 := by exact prefixLift 6071731
  have htrace : WordTrace (prefixWord ++ tailWord_6071731) baseStart_6071731 baseEnd_6071731 := by
    simpa [prefixWord, tailWord_6071731, baseEnd_6071731] using wordTrace_append hprefix tailTrace_6071731
  have hstable : (prefixWord ++ tailWord_6071731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071731).length < 2 ^ (prefixWord ++ tailWord_6071731).sum := by decide
  have hdescent : baseEnd_6071731 < baseStart_6071731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071825 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_6071825 : Nat := 118140960795 + 6071825 * 2 ^ 59
def prefixEnd_6071825 : Nat := 4983230072969 + 3 ^ 40 * 6071825 * 2
def baseEnd_6071825 : Nat := 3117764674985811690463691

theorem tailTrace_6071825 : CollatzResearch.WordTrace tailWord_6071825 prefixEnd_6071825 3117764674985811690463691 := by
  unfold tailWord_6071825
  simp only [CollatzResearch.WordTrace]
  refine ⟨221457651227822484996504929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147638434151881656664336619 221457651227822484996504929)
  ·
    refine ⟨166093238420866863747378697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221457651227822484996504929 166093238420866863747378697)
    ·
      refine ⟨124569928815650147810534023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166093238420866863747378697 124569928815650147810534023)
      ·
        refine ⟨186854893223475221715801035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124569928815650147810534023 186854893223475221715801035)
        ·
          refine ⟨280282339835212832573701553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186854893223475221715801035 280282339835212832573701553)
          ·
            refine ⟨210211754876409624430276165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280282339835212832573701553 210211754876409624430276165)
            ·
              refine ⟨39414704039326804580676781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210211754876409624430276165 39414704039326804580676781)
              ·
                refine ⟨14780514014747551717753793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39414704039326804580676781 14780514014747551717753793)
                ·
                  refine ⟨11085385511060663788315345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14780514014747551717753793 11085385511060663788315345)
                  ·
                    refine ⟨8314039133295497841236509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11085385511060663788315345 8314039133295497841236509)
                    ·
                      refine ⟨3117764674985811690463691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8314039133295497841236509 3117764674985811690463691)
                      ·
                        rfl

theorem cell23_6071825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_6071825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071825 prefixEnd_6071825 := by exact prefixLift 6071825
  have htrace : WordTrace (prefixWord ++ tailWord_6071825) baseStart_6071825 baseEnd_6071825 := by
    simpa [prefixWord, tailWord_6071825, baseEnd_6071825] using wordTrace_append hprefix tailTrace_6071825
  have hstable : (prefixWord ++ tailWord_6071825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071825).length < 2 ^ (prefixWord ++ tailWord_6071825).sum := by decide
  have hdescent : baseEnd_6071825 < baseStart_6071825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071858 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_6071858 : Nat := 118140960795 + 6071858 * 2 ^ 59
def prefixEnd_6071858 : Nat := 4983230072969 + 3 ^ 40 * 6071858 * 2
def baseEnd_6071858 : Nat := 1039260539949136687117013

theorem tailTrace_6071858 : CollatzResearch.WordTrace tailWord_6071858 prefixEnd_6071858 1039260539949136687117013 := by
  unfold tailWord_6071858
  simp only [CollatzResearch.WordTrace]
  refine ⟨55364713709175732908114057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147639236557801954421637485 55364713709175732908114057)
  ·
    refine ⟨41523535281881799681085543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55364713709175732908114057 41523535281881799681085543)
    ·
      refine ⟨62285302922822699521628315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41523535281881799681085543 62285302922822699521628315)
      ·
        refine ⟨93427954384234049282442473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62285302922822699521628315 93427954384234049282442473)
        ·
          refine ⟨70070965788175536961831855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93427954384234049282442473 70070965788175536961831855)
          ·
            refine ⟨105106448682263305442747783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70070965788175536961831855 105106448682263305442747783)
            ·
              refine ⟨157659673023394958164121675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105106448682263305442747783 157659673023394958164121675)
              ·
                refine ⟨236489509535092437246182513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157659673023394958164121675 236489509535092437246182513)
                ·
                  refine ⟨177367132151319327934636885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236489509535092437246182513 177367132151319327934636885)
                  ·
                    refine ⟨1039260539949136687117013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177367132151319327934636885 1039260539949136687117013)
                    ·
                      rfl

theorem cell23_6071858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_6071858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071858 prefixEnd_6071858 := by exact prefixLift 6071858
  have htrace : WordTrace (prefixWord ++ tailWord_6071858) baseStart_6071858 baseEnd_6071858 := by
    simpa [prefixWord, tailWord_6071858, baseEnd_6071858] using wordTrace_append hprefix tailTrace_6071858
  have hstable : (prefixWord ++ tailWord_6071858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071858).length < 2 ^ (prefixWord ++ tailWord_6071858).sum := by decide
  have hdescent : baseEnd_6071858 < baseStart_6071858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071889 : List Nat := [1, 2, 2, 1, 3, 2, 2, 5, 1, 1, 3]
def baseStart_6071889 : Nat := 118140960795 + 6071889 * 2 ^ 59
def prefixEnd_6071889 : Nat := 4983230072969 + 3 ^ 40 * 6071889 * 2
def baseEnd_6071889 : Nat := 3117797537747699440063397

theorem tailTrace_6071889 : CollatzResearch.WordTrace tailWord_6071889 prefixEnd_6071889 3117797537747699440063397 := by
  unfold tailWord_6071889
  simp only [CollatzResearch.WordTrace]
  refine ⟨221459985499590623926834721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147639990333060415951223147 221459985499590623926834721)
  ·
    refine ⟨166094989124692967945126041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221459985499590623926834721 166094989124692967945126041)
    ·
      refine ⟨124571241843519725958844531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166094989124692967945126041 124571241843519725958844531)
      ·
        refine ⟨186856862765279588938266797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124571241843519725958844531 186856862765279588938266797)
        ·
          refine ⟨70071323536979845851850049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186856862765279588938266797 70071323536979845851850049)
          ·
            refine ⟨52553492652734884388887537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70071323536979845851850049 52553492652734884388887537)
            ·
              refine ⟨39415119489551163291665653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52553492652734884388887537 39415119489551163291665653)
              ·
                refine ⟨3695167452145421558593655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39415119489551163291665653 3695167452145421558593655)
                ·
                  refine ⟨5542751178218132337890483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695167452145421558593655 5542751178218132337890483)
                  ·
                    refine ⟨8314126767327198506835725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5542751178218132337890483 8314126767327198506835725)
                    ·
                      refine ⟨3117797537747699440063397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8314126767327198506835725 3117797537747699440063397)
                      ·
                        rfl

theorem cell23_6071889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_6071889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071889 prefixEnd_6071889 := by exact prefixLift 6071889
  have htrace : WordTrace (prefixWord ++ tailWord_6071889) baseStart_6071889 baseEnd_6071889 := by
    simpa [prefixWord, tailWord_6071889, baseEnd_6071889] using wordTrace_append hprefix tailTrace_6071889
  have hstable : (prefixWord ++ tailWord_6071889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071889).length < 2 ^ (prefixWord ++ tailWord_6071889).sum := by decide
  have hdescent : baseEnd_6071889 < baseStart_6071889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071912 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_6071912 : Nat := 118140960795 + 6071912 * 2 ^ 59
def prefixEnd_6071912 : Nat := 4983230072969 + 3 ^ 40 * 6071912 * 2
def baseEnd_6071912 : Nat := 3117809347802752850075791

theorem tailTrace_6071912 : CollatzResearch.WordTrace tailWord_6071912 prefixEnd_6071912 3117809347802752850075791 := by
  unfold tailWord_6071912
  simp only [CollatzResearch.WordTrace]
  refine ⟨110730412189253649427460995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147640549585671532569947993 110730412189253649427460995)
  ·
    refine ⟨166095618283880474141191493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110730412189253649427460995 166095618283880474141191493)
    ·
      refine ⟨31142928428227588901473405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166095618283880474141191493 31142928428227588901473405)
      ·
        refine ⟨11678598160585345838052527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31142928428227588901473405 11678598160585345838052527)
        ·
          refine ⟨17517897240878018757078791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11678598160585345838052527 17517897240878018757078791)
          ·
            refine ⟨26276845861317028135618187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17517897240878018757078791 26276845861317028135618187)
            ·
              refine ⟨39415268791975542203427281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26276845861317028135618187 39415268791975542203427281)
              ·
                refine ⟨29561451593981656652570461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39415268791975542203427281 29561451593981656652570461)
                ·
                  refine ⟨11085544347743121244713923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29561451593981656652570461 11085544347743121244713923)
                  ·
                    refine ⟨16628316521614681867070885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11085544347743121244713923 16628316521614681867070885)
                    ·
                      refine ⟨3117809347802752850075791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16628316521614681867070885 3117809347802752850075791)
                      ·
                        rfl

theorem cell23_6071912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_6071912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071912 prefixEnd_6071912 := by exact prefixLift 6071912
  have htrace : WordTrace (prefixWord ++ tailWord_6071912) baseStart_6071912 baseEnd_6071912 := by
    simpa [prefixWord, tailWord_6071912, baseEnd_6071912] using wordTrace_append hprefix tailTrace_6071912
  have hstable : (prefixWord ++ tailWord_6071912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071912).length < 2 ^ (prefixWord ++ tailWord_6071912).sum := by decide
  have hdescent : baseEnd_6071912 < baseStart_6071912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071922 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_6071922 : Nat := 118140960795 + 6071922 * 2 ^ 59
def prefixEnd_6071922 : Nat := 4983230072969 + 3 ^ 40 * 6071922 * 2
def baseEnd_6071922 : Nat := 1039271494203099270316915

theorem tailTrace_6071922 : CollatzResearch.WordTrace tailWord_6071922 prefixEnd_6071922 1039271494203099270316915 := by
  unfold tailWord_6071922
  simp only [CollatzResearch.WordTrace]
  refine ⟨55365297277117767640696505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147640792738980713708524013 55365297277117767640696505)
  ·
    refine ⟨41523972957838325730522379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55365297277117767640696505 41523972957838325730522379)
    ·
      refine ⟨62285959436757488595783569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41523972957838325730522379 62285959436757488595783569)
      ·
        refine ⟨46714469577568116446837677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62285959436757488595783569 46714469577568116446837677)
        ·
          refine ⟨17517926091588043667564129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46714469577568116446837677 17517926091588043667564129)
          ·
            refine ⟨13138444568691032750673097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17517926091588043667564129 13138444568691032750673097)
            ·
              refine ⟨9853833426518274563004823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13138444568691032750673097 9853833426518274563004823)
              ·
                refine ⟨14780750139777411844507235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9853833426518274563004823 14780750139777411844507235)
                ·
                  refine ⟨22171125209666117766760853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14780750139777411844507235 22171125209666117766760853)
                  ·
                    refine ⟨1039271494203099270316915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22171125209666117766760853 1039271494203099270316915)
                    ·
                      rfl

theorem cell23_6071922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_6071922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071922 prefixEnd_6071922 := by exact prefixLift 6071922
  have htrace : WordTrace (prefixWord ++ tailWord_6071922) baseStart_6071922 baseEnd_6071922 := by
    simpa [prefixWord, tailWord_6071922, baseEnd_6071922] using wordTrace_append hprefix tailTrace_6071922
  have hstable : (prefixWord ++ tailWord_6071922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071922).length < 2 ^ (prefixWord ++ tailWord_6071922).sum := by decide
  have hdescent : baseEnd_6071922 < baseStart_6071922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071929 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 3, 2, 2]
def baseStart_6071929 : Nat := 118140960795 + 6071929 * 2 ^ 59
def prefixEnd_6071929 : Nat := 4983230072969 + 3 ^ 40 * 6071929 * 2
def baseEnd_6071929 : Nat := 3117818076973879283563213

theorem tailTrace_6071929 : CollatzResearch.WordTrace tailWord_6071929 prefixEnd_6071929 3117818076973879283563213 := by
  unfold tailWord_6071929
  simp only [CollatzResearch.WordTrace]
  refine ⟨221461444419445710758290841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147640962946297140505527227 221461444419445710758290841)
  ·
    refine ⟨166096083314584283068718131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221461444419445710758290841 166096083314584283068718131)
    ·
      refine ⟨249144124971876424603077197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166096083314584283068718131 249144124971876424603077197)
      ·
        refine ⟨93429046864453659226153949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249144124971876424603077197 93429046864453659226153949)
        ·
          refine ⟨35035892574170122209807731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93429046864453659226153949 35035892574170122209807731)
          ·
            refine ⟨52553838861255183314711597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35035892574170122209807731 52553838861255183314711597)
            ·
              refine ⟨19707689572970693743016849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52553838861255183314711597 19707689572970693743016849)
              ·
                refine ⟨14780767179728020307262637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19707689572970693743016849 14780767179728020307262637)
                ·
                  refine ⟨5542787692398007615223489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14780767179728020307262637 5542787692398007615223489)
                  ·
                    refine ⟨4157090769298505711417617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5542787692398007615223489 4157090769298505711417617)
                    ·
                      refine ⟨3117818076973879283563213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157090769298505711417617 3117818076973879283563213)
                      ·
                        rfl

theorem cell23_6071929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_6071929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071929 prefixEnd_6071929 := by exact prefixLift 6071929
  have htrace : WordTrace (prefixWord ++ tailWord_6071929) baseStart_6071929 baseEnd_6071929 := by
    simpa [prefixWord, tailWord_6071929, baseEnd_6071929] using wordTrace_append hprefix tailTrace_6071929
  have hstable : (prefixWord ++ tailWord_6071929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071929).length < 2 ^ (prefixWord ++ tailWord_6071929).sum := by decide
  have hdescent : baseEnd_6071929 < baseStart_6071929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071932 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_6071932 : Nat := 118140960795 + 6071932 * 2 ^ 59
def prefixEnd_6071932 : Nat := 4983230072969 + 3 ^ 40 * 6071932 * 2
def baseEnd_6071932 : Nat := 3117819617415842771825699

theorem tailTrace_6071932 : CollatzResearch.WordTrace tailWord_6071932 prefixEnd_6071932 3117819617415842771825699 := by
  unfold tailWord_6071932
  simp only [CollatzResearch.WordTrace]
  refine ⟨110730776919217421135325025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147641035892289894847100033 110730776919217421135325025)
  ·
    refine ⟨83048082689413065851493769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110730776919217421135325025 83048082689413065851493769)
    ·
      refine ⟨62286062017059799388620327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83048082689413065851493769 62286062017059799388620327)
      ·
        refine ⟨93429093025589699082930491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62286062017059799388620327 93429093025589699082930491)
        ·
          refine ⟨140143639538384548624395737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93429093025589699082930491 140143639538384548624395737)
          ·
            refine ⟨105107729653788411468296803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140143639538384548624395737 105107729653788411468296803)
            ·
              refine ⟨157661594480682617202445205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105107729653788411468296803 157661594480682617202445205)
              ·
                refine ⟨7390387241281997681364619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157661594480682617202445205 7390387241281997681364619)
                ·
                  refine ⟨11085580861922996522046929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7390387241281997681364619 11085580861922996522046929)
                  ·
                    refine ⟨8314185646442247391535197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11085580861922996522046929 8314185646442247391535197)
                    ·
                      refine ⟨3117819617415842771825699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8314185646442247391535197 3117819617415842771825699)
                      ·
                        rfl

theorem cell23_6071932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_6071932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071932 prefixEnd_6071932 := by exact prefixLift 6071932
  have htrace : WordTrace (prefixWord ++ tailWord_6071932) baseStart_6071932 baseEnd_6071932 := by
    simpa [prefixWord, tailWord_6071932, baseEnd_6071932] using wordTrace_append hprefix tailTrace_6071932
  have hstable : (prefixWord ++ tailWord_6071932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071932).length < 2 ^ (prefixWord ++ tailWord_6071932).sum := by decide
  have hdescent : baseEnd_6071932 < baseStart_6071932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071946 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_6071946 : Nat := 118140960795 + 6071946 * 2 ^ 59
def prefixEnd_6071946 : Nat := 4983230072969 + 3 ^ 40 * 6071946 * 2
def baseEnd_6071946 : Nat := 3117826806145005717050635

theorem tailTrace_6071946 : CollatzResearch.WordTrace tailWord_6071946 prefixEnd_6071946 3117826806145005717050635 := by
  unfold tailWord_6071946
  simp only [CollatzResearch.WordTrace]
  refine ⟨55365516115096030665414923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147641376306922748441106461 55365516115096030665414923)
  ·
    refine ⟨83048274172644045998122385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55365516115096030665414923 83048274172644045998122385)
    ·
      refine ⟨62286205629483034498591789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83048274172644045998122385 62286205629483034498591789)
      ·
        refine ⟨23357327111056137936971921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62286205629483034498591789 23357327111056137936971921)
        ·
          refine ⟨17517995333292103452728941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23357327111056137936971921 17517995333292103452728941)
          ·
            refine ⟨6569248249984538794773353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17517995333292103452728941 6569248249984538794773353)
            ·
              refine ⟨4926936187488404096080015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6569248249984538794773353 4926936187488404096080015)
              ·
                refine ⟨7390404281232606144120023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4926936187488404096080015 7390404281232606144120023)
                ·
                  refine ⟨11085606421848909216180035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7390404281232606144120023 11085606421848909216180035)
                  ·
                    refine ⟨16628409632773363824270053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11085606421848909216180035 16628409632773363824270053)
                    ·
                      refine ⟨3117826806145005717050635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16628409632773363824270053 3117826806145005717050635)
                      ·
                        rfl

theorem cell23_6071946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_6071946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071946 prefixEnd_6071946 := by exact prefixLift 6071946
  have htrace : WordTrace (prefixWord ++ tailWord_6071946) baseStart_6071946 baseEnd_6071946 := by
    simpa [prefixWord, tailWord_6071946, baseEnd_6071946] using wordTrace_append hprefix tailTrace_6071946
  have hstable : (prefixWord ++ tailWord_6071946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071946).length < 2 ^ (prefixWord ++ tailWord_6071946).sum := by decide
  have hdescent : baseEnd_6071946 < baseStart_6071946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6071976 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6071976 : Nat := 118140960795 + 6071976 * 2 ^ 59
def prefixEnd_6071976 : Nat := 4983230072969 + 3 ^ 40 * 6071976 * 2
def baseEnd_6071976 : Nat := 3117842210564640599675497

theorem tailTrace_6071976 : CollatzResearch.WordTrace tailWord_6071976 prefixEnd_6071976 3117842210564640599675497 := by
  unfold tailWord_6071976
  simp only [CollatzResearch.WordTrace]
  refine ⟨110731579325137718892625891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147642105766850291856834521 110731579325137718892625891)
  ·
    refine ⟨166097368987706578338938837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110731579325137718892625891 166097368987706578338938837)
    ·
      refine ⟨3892907085649372929818879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 166097368987706578338938837 3892907085649372929818879)
      ·
        refine ⟨5839360628474059394728319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3892907085649372929818879 5839360628474059394728319)
        ·
          refine ⟨8759040942711089092092479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5839360628474059394728319 8759040942711089092092479)
          ·
            refine ⟨13138561414066633638138719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8759040942711089092092479 13138561414066633638138719)
            ·
              refine ⟨19707842121099950457208079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13138561414066633638138719 19707842121099950457208079)
              ·
                refine ⟨29561763181649925685812119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19707842121099950457208079 29561763181649925685812119)
                ·
                  refine ⟨44342644772474888528718179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29561763181649925685812119 44342644772474888528718179)
                  ·
                    refine ⟨66513967158712332793077269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44342644772474888528718179 66513967158712332793077269)
                    ·
                      refine ⟨3117842210564640599675497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66513967158712332793077269 3117842210564640599675497)
                      ·
                        rfl

theorem cell23_6071976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6071976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6071976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6071976 prefixEnd_6071976 := by exact prefixLift 6071976
  have htrace : WordTrace (prefixWord ++ tailWord_6071976) baseStart_6071976 baseEnd_6071976 := by
    simpa [prefixWord, tailWord_6071976, baseEnd_6071976] using wordTrace_append hprefix tailTrace_6071976
  have hstable : (prefixWord ++ tailWord_6071976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6071976).length < 2 ^ (prefixWord ++ tailWord_6071976).sum := by decide
  have hdescent : baseEnd_6071976 < baseStart_6071976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6071976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072005 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_6072005 : Nat := 118140960795 + 6072005 * 2 ^ 59
def prefixEnd_6072005 : Nat := 4983230072969 + 3 ^ 40 * 6072005 * 2
def baseEnd_6072005 : Nat := 3117857101503620986212863

theorem tailTrace_6072005 : CollatzResearch.WordTrace tailWord_6072005 prefixEnd_6072005 3117857101503620986212863 := by
  unfold tailWord_6072005
  simp only [CollatzResearch.WordTrace]
  refine ⟨221464216367170375738057469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147642810911446917158704979 221464216367170375738057469)
  ·
    refine ⟨83049081137688890901771551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221464216367170375738057469 83049081137688890901771551)
    ·
      refine ⟨124573621706533336352657327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83049081137688890901771551 124573621706533336352657327)
      ·
        refine ⟨186860432559800004528985991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124573621706533336352657327 186860432559800004528985991)
        ·
          refine ⟨280290648839700006793478987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186860432559800004528985991 280290648839700006793478987)
          ·
            refine ⟨420435973259550010190218481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280290648839700006793478987 420435973259550010190218481)
            ·
              refine ⟨315326979944662507642663861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420435973259550010190218481 315326979944662507642663861)
              ·
                refine ⟨29561904369812110091499737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315326979944662507642663861 29561904369812110091499737)
                ·
                  refine ⟨22171428277359082568624803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29561904369812110091499737 22171428277359082568624803)
                  ·
                    refine ⟨33257142416038623852937205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22171428277359082568624803 33257142416038623852937205)
                    ·
                      refine ⟨3117857101503620986212863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33257142416038623852937205 3117857101503620986212863)
                      ·
                        rfl

theorem cell23_6072005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_6072005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072005 prefixEnd_6072005 := by exact prefixLift 6072005
  have htrace : WordTrace (prefixWord ++ tailWord_6072005) baseStart_6072005 baseEnd_6072005 := by
    simpa [prefixWord, tailWord_6072005, baseEnd_6072005] using wordTrace_append hprefix tailTrace_6072005
  have hstable : (prefixWord ++ tailWord_6072005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072005).length < 2 ^ (prefixWord ++ tailWord_6072005).sum := by decide
  have hdescent : baseEnd_6072005 < baseStart_6072005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072015 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_6072015 : Nat := 118140960795 + 6072015 * 2 ^ 59
def prefixEnd_6072015 : Nat := 4983230072969 + 3 ^ 40 * 6072015 * 2
def baseEnd_6072015 : Nat := 3117862236310165947087817

theorem tailTrace_6072015 : CollatzResearch.WordTrace tailWord_6072015 prefixEnd_6072015 3117862236310165947087817 := by
  unfold tailWord_6072015
  simp only [CollatzResearch.WordTrace]
  refine ⟨221464581097134147445921499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147643054064756098297280999 221464581097134147445921499)
  ·
    refine ⟨332196871645701221168882249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221464581097134147445921499 332196871645701221168882249)
    ·
      refine ⟨249147653734275915876661687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332196871645701221168882249 249147653734275915876661687)
      ·
        refine ⟨373721480601413873814992531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249147653734275915876661687 373721480601413873814992531)
        ·
          refine ⟨560582220902120810722488797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373721480601413873814992531 560582220902120810722488797)
          ·
            refine ⟨210218332838295304020933299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560582220902120810722488797 210218332838295304020933299)
            ·
              refine ⟨315327499257442956031399949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210218332838295304020933299 315327499257442956031399949)
              ·
                refine ⟨118247812221541108511774981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315327499257442956031399949 118247812221541108511774981)
                ·
                  refine ⟨22171464791538957845957809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118247812221541108511774981 22171464791538957845957809)
                  ·
                    refine ⟨16628598593654218384468357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22171464791538957845957809 16628598593654218384468357)
                    ·
                      refine ⟨3117862236310165947087817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16628598593654218384468357 3117862236310165947087817)
                      ·
                        rfl

theorem cell23_6072015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_6072015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072015 prefixEnd_6072015 := by exact prefixLift 6072015
  have htrace : WordTrace (prefixWord ++ tailWord_6072015) baseStart_6072015 baseEnd_6072015 := by
    simpa [prefixWord, tailWord_6072015, baseEnd_6072015] using wordTrace_append hprefix tailTrace_6072015
  have hstable : (prefixWord ++ tailWord_6072015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072015).length < 2 ^ (prefixWord ++ tailWord_6072015).sum := by decide
  have hdescent : baseEnd_6072015 < baseStart_6072015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072036 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_6072036 : Nat := 118140960795 + 6072036 * 2 ^ 59
def prefixEnd_6072036 : Nat := 4983230072969 + 3 ^ 40 * 6072036 * 2
def baseEnd_6072036 : Nat := 3117873019403910364925221

theorem tailTrace_6072036 : CollatzResearch.WordTrace tailWord_6072036 prefixEnd_6072036 3117873019403910364925221 := by
  unfold tailWord_6072036
  simp only [CollatzResearch.WordTrace]
  refine ⟨110732673515029034016217981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147643564686705378688290641 110732673515029034016217981)
  ·
    refine ⟨41524752568135887756081743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110732673515029034016217981 41524752568135887756081743)
    ·
      refine ⟨62287128852203831634122615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41524752568135887756081743 62287128852203831634122615)
      ·
        refine ⟨93430693278305747451183923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62287128852203831634122615 93430693278305747451183923)
        ·
          refine ⟨140146039917458621176775885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93430693278305747451183923 140146039917458621176775885)
          ·
            refine ⟨52554764969046982941290957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140146039917458621176775885 52554764969046982941290957)
            ·
              refine ⟨19708036863392618602984109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52554764969046982941290957 19708036863392618602984109)
              ·
                refine ⟨7390513823772231976119041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19708036863392618602984109 7390513823772231976119041)
                ·
                  refine ⟨5542885367829173982089281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7390513823772231976119041 5542885367829173982089281)
                  ·
                    refine ⟨4157164025871880486566961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5542885367829173982089281 4157164025871880486566961)
                    ·
                      refine ⟨3117873019403910364925221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157164025871880486566961 3117873019403910364925221)
                      ·
                        rfl

theorem cell23_6072036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_6072036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072036 prefixEnd_6072036 := by exact prefixLift 6072036
  have htrace : WordTrace (prefixWord ++ tailWord_6072036) baseStart_6072036 baseEnd_6072036 := by
    simpa [prefixWord, tailWord_6072036, baseEnd_6072036] using wordTrace_append hprefix tailTrace_6072036
  have hstable : (prefixWord ++ tailWord_6072036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072036).length < 2 ^ (prefixWord ++ tailWord_6072036).sum := by decide
  have hdescent : baseEnd_6072036 < baseStart_6072036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072055 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 1, 7]
def baseStart_6072055 : Nat := 118140960795 + 6072055 * 2 ^ 59
def prefixEnd_6072055 : Nat := 4983230072969 + 3 ^ 40 * 6072055 * 2
def baseEnd_6072055 : Nat := 1039294258512115263529211

theorem tailTrace_6072055 : CollatzResearch.WordTrace tailWord_6072055 prefixEnd_6072055 1039294258512115263529211 := by
  unfold tailWord_6072055
  simp only [CollatzResearch.WordTrace]
  refine ⟨221466040016989234277377619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147644026677992822851585079 221466040016989234277377619)
  ·
    refine ⟨332199060025483851416066429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221466040016989234277377619 332199060025483851416066429)
    ·
      refine ⟨124574647509556444281024911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332199060025483851416066429 124574647509556444281024911)
      ·
        refine ⟨186861971264334666421537367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124574647509556444281024911 186861971264334666421537367)
        ·
          refine ⟨280292956896501999632306051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186861971264334666421537367 280292956896501999632306051)
          ·
            refine ⟨420439435344752999448459077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280292956896501999632306051 420439435344752999448459077)
            ·
              refine ⟨78832394127141187396586077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 420439435344752999448459077 78832394127141187396586077)
              ·
                refine ⟨29562147797677945273719779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78832394127141187396586077 29562147797677945273719779)
                ·
                  refine ⟨44343221696516917910579669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29562147797677945273719779 44343221696516917910579669)
                  ·
                    refine ⟨1039294258512115263529211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44343221696516917910579669 1039294258512115263529211)
                    ·
                      rfl

theorem cell23_6072055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_6072055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072055 prefixEnd_6072055 := by exact prefixLift 6072055
  have htrace : WordTrace (prefixWord ++ tailWord_6072055) baseStart_6072055 baseEnd_6072055 := by
    simpa [prefixWord, tailWord_6072055, baseEnd_6072055] using wordTrace_append hprefix tailTrace_6072055
  have hstable : (prefixWord ++ tailWord_6072055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072055).length < 2 ^ (prefixWord ++ tailWord_6072055).sum := by decide
  have hdescent : baseEnd_6072055 < baseStart_6072055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072072 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 2, 5]
def baseStart_6072072 : Nat := 118140960795 + 6072072 * 2 ^ 59
def prefixEnd_6072072 : Nat := 4983230072969 + 3 ^ 40 * 6072072 * 2
def baseEnd_6072072 : Nat := 1039297168235824074691685

theorem tailTrace_6072072 : CollatzResearch.WordTrace tailWord_6072072 prefixEnd_6072072 1039297168235824074691685 := by
  unfold tailWord_6072072
  simp only [CollatzResearch.WordTrace]
  refine ⟨110733330028963823090373235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147644440038618430787164313 110733330028963823090373235)
  ·
    refine ⟨166099995043445734635559853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110733330028963823090373235 166099995043445734635559853)
    ·
      refine ⟨62287498141292150488334945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166099995043445734635559853 62287498141292150488334945)
      ·
        refine ⟨46715623605969112866251209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62287498141292150488334945 46715623605969112866251209)
        ·
          refine ⟨35036717704476834649688407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46715623605969112866251209 35036717704476834649688407)
          ·
            refine ⟨52555076556715251974532611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35036717704476834649688407 52555076556715251974532611)
            ·
              refine ⟨78832614835072877961798917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52555076556715251974532611 78832614835072877961798917)
              ·
                refine ⟨14781115281576164617837297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78832614835072877961798917 14781115281576164617837297)
                ·
                  refine ⟨11085836461182123463377973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14781115281576164617837297 11085836461182123463377973)
                  ·
                    refine ⟨1039297168235824074691685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11085836461182123463377973 1039297168235824074691685)
                    ·
                      rfl

theorem cell23_6072072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_6072072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072072 prefixEnd_6072072 := by exact prefixLift 6072072
  have htrace : WordTrace (prefixWord ++ tailWord_6072072) baseStart_6072072 baseEnd_6072072 := by
    simpa [prefixWord, tailWord_6072072, baseEnd_6072072] using wordTrace_append hprefix tailTrace_6072072
  have hstable : (prefixWord ++ tailWord_6072072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072072).length < 2 ^ (prefixWord ++ tailWord_6072072).sum := by decide
  have hdescent : baseEnd_6072072 < baseStart_6072072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072092 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_6072092 : Nat := 118140960795 + 6072092 * 2 ^ 59
def prefixEnd_6072092 : Nat := 4983230072969 + 3 ^ 40 * 6072092 * 2
def baseEnd_6072092 : Nat := 3117901774320562145824963

theorem tailTrace_6072092 : CollatzResearch.WordTrace tailWord_6072092 prefixEnd_6072092 3117901774320562145824963 := by
  unfold tailWord_6072092
  simp only [CollatzResearch.WordTrace]
  refine ⟨110733694758927594798237265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147644926345236793064316353 110733694758927594798237265)
  ·
    refine ⟨83050271069195696098677949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110733694758927594798237265 83050271069195696098677949)
    ·
      refine ⟨31143851650948386037004231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83050271069195696098677949 31143851650948386037004231)
      ·
        refine ⟨46715777476422579055506347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31143851650948386037004231 46715777476422579055506347)
        ·
          refine ⟨70073666214633868583259521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46715777476422579055506347 70073666214633868583259521)
          ·
            refine ⟨52555249660975401437444641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70073666214633868583259521 52555249660975401437444641)
            ·
              refine ⟨39416437245731551078083481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52555249660975401437444641 39416437245731551078083481)
              ·
                refine ⟨29562327934298663308562611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39416437245731551078083481 29562327934298663308562611)
                ·
                  refine ⟨44343491901447994962843917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29562327934298663308562611 44343491901447994962843917)
                  ·
                    refine ⟨16628809463042998111066469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44343491901447994962843917 16628809463042998111066469)
                    ·
                      refine ⟨3117901774320562145824963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16628809463042998111066469 3117901774320562145824963)
                      ·
                        rfl

theorem cell23_6072092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_6072092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072092 prefixEnd_6072092 := by exact prefixLift 6072092
  have htrace : WordTrace (prefixWord ++ tailWord_6072092) baseStart_6072092 baseEnd_6072092 := by
    simpa [prefixWord, tailWord_6072092, baseEnd_6072092] using wordTrace_append hprefix tailTrace_6072092
  have hstable : (prefixWord ++ tailWord_6072092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072092).length < 2 ^ (prefixWord ++ tailWord_6072092).sum := by decide
  have hdescent : baseEnd_6072092 < baseStart_6072092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_6072105 : Nat := 118140960795 + 6072105 * 2 ^ 59
def prefixEnd_6072105 : Nat := 4983230072969 + 3 ^ 40 * 6072105 * 2
def baseEnd_6072105 : Nat := 3117908449569070594962403

theorem tailTrace_6072105 : CollatzResearch.WordTrace tailWord_6072105 prefixEnd_6072105 3117908449569070594962403 := by
  unfold tailWord_6072105
  simp only [CollatzResearch.WordTrace]
  refine ⟨221467863666808092816697769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147645242444538728544465179 221467863666808092816697769)
  ·
    refine ⟨166100897750106069612523327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221467863666808092816697769 166100897750106069612523327)
    ·
      refine ⟨249151346625159104418784991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166100897750106069612523327 249151346625159104418784991)
      ·
        refine ⟨373727019937738656628177487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249151346625159104418784991 373727019937738656628177487)
        ·
          refine ⟨560590529906607984942266231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373727019937738656628177487 560590529906607984942266231)
          ·
            refine ⟨840885794859911977413399347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560590529906607984942266231 840885794859911977413399347)
            ·
              refine ⟨1261328692289867966120099021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840885794859911977413399347 1261328692289867966120099021)
              ·
                refine ⟨472998259608700487295037133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261328692289867966120099021 472998259608700487295037133)
                ·
                  refine ⟨177374347353262682735638925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472998259608700487295037133 177374347353262682735638925)
                  ·
                    refine ⟨66515380257473506025864597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177374347353262682735638925 66515380257473506025864597)
                    ·
                      refine ⟨3117908449569070594962403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66515380257473506025864597 3117908449569070594962403)
                      ·
                        rfl

theorem cell23_6072105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_6072105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072105 prefixEnd_6072105 := by exact prefixLift 6072105
  have htrace : WordTrace (prefixWord ++ tailWord_6072105) baseStart_6072105 baseEnd_6072105 := by
    simpa [prefixWord, tailWord_6072105, baseEnd_6072105] using wordTrace_append hprefix tailTrace_6072105
  have hstable : (prefixWord ++ tailWord_6072105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072105).length < 2 ^ (prefixWord ++ tailWord_6072105).sum := by decide
  have hdescent : baseEnd_6072105 < baseStart_6072105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072122 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_6072122 : Nat := 118140960795 + 6072122 * 2 ^ 59
def prefixEnd_6072122 : Nat := 4983230072969 + 3 ^ 40 * 6072122 * 2
def baseEnd_6072122 : Nat := 3117917178740197028449825

theorem tailTrace_6072122 : CollatzResearch.WordTrace tailWord_6072122 prefixEnd_6072122 3117917178740197028449825 := by
  unfold tailWord_6072122
  simp only [CollatzResearch.WordTrace]
  refine ⟨55367120926936626180016655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147645655805164336480044413 55367120926936626180016655)
  ·
    refine ⟨83050681390404939270024983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55367120926936626180016655 83050681390404939270024983)
    ·
      refine ⟨124576022085607408905037475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83050681390404939270024983 124576022085607408905037475)
      ·
        refine ⟨186864033128411113357556213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124576022085607408905037475 186864033128411113357556213)
        ·
          refine ⟨17518503105788541877270895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 186864033128411113357556213 17518503105788541877270895)
          ·
            refine ⟨26277754658682812815906343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17518503105788541877270895 26277754658682812815906343)
            ·
              refine ⟨39416631988024219223859515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26277754658682812815906343 39416631988024219223859515)
              ·
                refine ⟨59124947982036328835789273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39416631988024219223859515 59124947982036328835789273)
                ·
                  refine ⟨44343710986527246626841955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59124947982036328835789273 44343710986527246626841955)
                  ·
                    refine ⟨66515566479790869940262933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44343710986527246626841955 66515566479790869940262933)
                    ·
                      refine ⟨3117917178740197028449825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66515566479790869940262933 3117917178740197028449825)
                      ·
                        rfl

theorem cell23_6072122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_6072122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072122 prefixEnd_6072122 := by exact prefixLift 6072122
  have htrace : WordTrace (prefixWord ++ tailWord_6072122) baseStart_6072122 baseEnd_6072122 := by
    simpa [prefixWord, tailWord_6072122, baseEnd_6072122] using wordTrace_append hprefix tailTrace_6072122
  have hstable : (prefixWord ++ tailWord_6072122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072122).length < 2 ^ (prefixWord ++ tailWord_6072122).sum := by decide
  have hdescent : baseEnd_6072122 < baseStart_6072122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072126 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_6072126 : Nat := 118140960795 + 6072126 * 2 ^ 59
def prefixEnd_6072126 : Nat := 4983230072969 + 3 ^ 40 * 6072126 * 2
def baseEnd_6072126 : Nat := 3117919232662815012799807

theorem tailTrace_6072126 : CollatzResearch.WordTrace tailWord_6072126 prefixEnd_6072126 3117919232662815012799807 := by
  unfold tailWord_6072126
  simp only [CollatzResearch.WordTrace]
  refine ⟨27683578699966501675401529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147645753066488008935474821 27683578699966501675401529)
  ·
    refine ⟨20762684024974876256551147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27683578699966501675401529 20762684024974876256551147)
    ·
      refine ⟨31144026037462314384826721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20762684024974876256551147 31144026037462314384826721)
      ·
        refine ⟨23358019528096735788620041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31144026037462314384826721 23358019528096735788620041)
        ·
          refine ⟨17518514646072551841465031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23358019528096735788620041 17518514646072551841465031)
          ·
            refine ⟨26277771969108827762197547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17518514646072551841465031 26277771969108827762197547)
            ·
              refine ⟨39416657953663241643296321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26277771969108827762197547 39416657953663241643296321)
              ·
                refine ⟨29562493465247431232472241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39416657953663241643296321 29562493465247431232472241)
                ·
                  refine ⟨22171870098935573424354181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29562493465247431232472241 22171870098935573424354181)
                  ·
                    refine ⟨4157225643550420017066409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22171870098935573424354181 4157225643550420017066409)
                    ·
                      refine ⟨3117919232662815012799807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157225643550420017066409 3117919232662815012799807)
                      ·
                        rfl

theorem cell23_6072126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_6072126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072126 prefixEnd_6072126 := by exact prefixLift 6072126
  have htrace : WordTrace (prefixWord ++ tailWord_6072126) baseStart_6072126 baseEnd_6072126 := by
    simpa [prefixWord, tailWord_6072126, baseEnd_6072126] using wordTrace_append hprefix tailTrace_6072126
  have hstable : (prefixWord ++ tailWord_6072126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072126).length < 2 ^ (prefixWord ++ tailWord_6072126).sum := by decide
  have hdescent : baseEnd_6072126 < baseStart_6072126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072136 : List Nat := [2, 1, 3, 1, 1, 4, 2, 4, 1, 4]
def baseStart_6072136 : Nat := 118140960795 + 6072136 * 2 ^ 59
def prefixEnd_6072136 : Nat := 4983230072969 + 3 ^ 40 * 6072136 * 2
def baseEnd_6072136 : Nat := 1039308122489786657891587

theorem tailTrace_6072136 : CollatzResearch.WordTrace tailWord_6072136 prefixEnd_6072136 1039308122489786657891587 := by
  unfold tailWord_6072136
  simp only [CollatzResearch.WordTrace]
  refine ⟨110734497164847892555538131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147645996219797190074050841 110734497164847892555538131)
  ·
    refine ⟨166101745747271838833307197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110734497164847892555538131 166101745747271838833307197)
    ·
      refine ⟨62288154655226939562490199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166101745747271838833307197 62288154655226939562490199)
      ·
        refine ⟨93432231982840409343735299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62288154655226939562490199 93432231982840409343735299)
        ·
          refine ⟨140148347974260614015602949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93432231982840409343735299 140148347974260614015602949)
          ·
            refine ⟨26277815245173865127925553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140148347974260614015602949 26277815245173865127925553)
            ·
              refine ⟨19708361433880398845944165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26277815245173865127925553 19708361433880398845944165)
              ·
                refine ⟨3695317768852574783614531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19708361433880398845944165 3695317768852574783614531)
                ·
                  refine ⟨5542976653278862175421797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695317768852574783614531 5542976653278862175421797)
                  ·
                    refine ⟨1039308122489786657891587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5542976653278862175421797 1039308122489786657891587)
                    ·
                      rfl

theorem cell23_6072136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_6072136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072136 prefixEnd_6072136 := by exact prefixLift 6072136
  have htrace : WordTrace (prefixWord ++ tailWord_6072136) baseStart_6072136 baseEnd_6072136 := by
    simpa [prefixWord, tailWord_6072136, baseEnd_6072136] using wordTrace_append hprefix tailTrace_6072136
  have hstable : (prefixWord ++ tailWord_6072136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072136).length < 2 ^ (prefixWord ++ tailWord_6072136).sum := by decide
  have hdescent : baseEnd_6072136 < baseStart_6072136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072169 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 6, 3, 2]
def baseStart_6072169 : Nat := 118140960795 + 6072169 * 2 ^ 59
def prefixEnd_6072169 : Nat := 4983230072969 + 3 ^ 40 * 6072169 * 2
def baseEnd_6072169 : Nat := 3117941312330958344562109

theorem tailTrace_6072169 : CollatzResearch.WordTrace tailWord_6072169 prefixEnd_6072169 3117941312330958344562109 := by
  unfold tailWord_6072169
  simp only [CollatzResearch.WordTrace]
  refine ⟨221470197938576231747027561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147646798625717487831351707 221470197938576231747027561)
  ·
    refine ⟨166102648453932173810270671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221470197938576231747027561 166102648453932173810270671)
    ·
      refine ⟨249153972680898260715406007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166102648453932173810270671 249153972680898260715406007)
      ·
        refine ⟨373730959021347391073109011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249153972680898260715406007 373730959021347391073109011)
        ·
          refine ⟨560596438532021086609663517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373730959021347391073109011 560596438532021086609663517)
          ·
            refine ⟨210223664449507907478623819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560596438532021086609663517 210223664449507907478623819)
            ·
              refine ⟨315335496674261861217935729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210223664449507907478623819 315335496674261861217935729)
              ·
                refine ⟨236501622505696395913451797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315335496674261861217935729 236501622505696395913451797)
                ·
                  refine ⟨11086013554954518558443053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236501622505696395913451797 11086013554954518558443053)
                  ·
                    refine ⟨4157255083107944459416145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11086013554954518558443053 4157255083107944459416145)
                    ·
                      refine ⟨3117941312330958344562109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157255083107944459416145 3117941312330958344562109)
                      ·
                        rfl

theorem cell23_6072169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 3, 2].length) (baseStart_6072169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072169 prefixEnd_6072169 := by exact prefixLift 6072169
  have htrace : WordTrace (prefixWord ++ tailWord_6072169) baseStart_6072169 baseEnd_6072169 := by
    simpa [prefixWord, tailWord_6072169, baseEnd_6072169] using wordTrace_append hprefix tailTrace_6072169
  have hstable : (prefixWord ++ tailWord_6072169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072169).length < 2 ^ (prefixWord ++ tailWord_6072169).sum := by decide
  have hdescent : baseEnd_6072169 < baseStart_6072169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072226 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_6072226 : Nat := 118140960795 + 6072226 * 2 ^ 59
def prefixEnd_6072226 : Nat := 4983230072969 + 3 ^ 40 * 6072226 * 2
def baseEnd_6072226 : Nat := 1039323526909421540516449

theorem tailTrace_6072226 : CollatzResearch.WordTrace tailWord_6072226 prefixEnd_6072226 1039323526909421540516449 := by
  unfold tailWord_6072226
  simp only [CollatzResearch.WordTrace]
  refine ⟨55368069224842432620463133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147648184599579820321235021 55368069224842432620463133)
  ·
    refine ⟨20763025959315912232673675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55368069224842432620463133 20763025959315912232673675)
    ·
      refine ⟨31144538938973868349010513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20763025959315912232673675 31144538938973868349010513)
      ·
        refine ⟨23358404204230401261757885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31144538938973868349010513 23358404204230401261757885)
        ·
          refine ⟨8759401576586400473159207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23358404204230401261757885 8759401576586400473159207)
          ·
            refine ⟨13139102364879600709738811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8759401576586400473159207 13139102364879600709738811)
            ·
              refine ⟨19708653547319401064608217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13139102364879600709738811 19708653547319401064608217)
              ·
                refine ⟨14781490160489550798456163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19708653547319401064608217 14781490160489550798456163)
                ·
                  refine ⟨22172235240734326197684245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14781490160489550798456163 22172235240734326197684245)
                  ·
                    refine ⟨1039323526909421540516449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22172235240734326197684245 1039323526909421540516449)
                    ·
                      rfl

theorem cell23_6072226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_6072226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072226 prefixEnd_6072226 := by exact prefixLift 6072226
  have htrace : WordTrace (prefixWord ++ tailWord_6072226) baseStart_6072226 baseEnd_6072226 := by
    simpa [prefixWord, tailWord_6072226, baseEnd_6072226] using wordTrace_append hprefix tailTrace_6072226
  have hstable : (prefixWord ++ tailWord_6072226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072226).length < 2 ^ (prefixWord ++ tailWord_6072226).sum := by decide
  have hdescent : baseEnd_6072226 < baseStart_6072226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072249 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 3]
def baseStart_6072249 : Nat := 118140960795 + 6072249 * 2 ^ 59
def prefixEnd_6072249 : Nat := 4983230072969 + 3 ^ 40 * 6072249 * 2
def baseEnd_6072249 : Nat := 3117982390783318031561741

theorem tailTrace_6072249 : CollatzResearch.WordTrace tailWord_6072249 prefixEnd_6072249 3117982390783318031561741 := by
  unfold tailWord_6072249
  simp only [CollatzResearch.WordTrace]
  refine ⟨221473115778286405409939801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147648743852190936939959867 221473115778286405409939801)
  ·
    refine ⟨166104836833714804057454851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221473115778286405409939801 166104836833714804057454851)
    ·
      refine ⟨249157255250572206086182277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166104836833714804057454851 249157255250572206086182277)
      ·
        refine ⟨46716985359482288641159177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249157255250572206086182277 46716985359482288641159177)
        ·
          refine ⟨35037739019611716480869383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46716985359482288641159177 35037739019611716480869383)
          ·
            refine ⟨52556608529417574721304075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35037739019611716480869383 52556608529417574721304075)
            ·
              refine ⟨78834912794126362081956113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52556608529417574721304075 78834912794126362081956113)
              ·
                refine ⟨59126184595594771561467085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78834912794126362081956113 59126184595594771561467085)
                ·
                  refine ⟨22172319223348039335550157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59126184595594771561467085 22172319223348039335550157)
                  ·
                    refine ⟨8314619708755514750831309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22172319223348039335550157 8314619708755514750831309)
                    ·
                      refine ⟨3117982390783318031561741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8314619708755514750831309 3117982390783318031561741)
                      ·
                        rfl

theorem cell23_6072249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_6072249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072249 prefixEnd_6072249 := by exact prefixLift 6072249
  have htrace : WordTrace (prefixWord ++ tailWord_6072249) baseStart_6072249 baseEnd_6072249 := by
    simpa [prefixWord, tailWord_6072249, baseEnd_6072249] using wordTrace_append hprefix tailTrace_6072249
  have hstable : (prefixWord ++ tailWord_6072249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072249).length < 2 ^ (prefixWord ++ tailWord_6072249).sum := by decide
  have hdescent : baseEnd_6072249 < baseStart_6072249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072259 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 9, 2]
def baseStart_6072259 : Nat := 118140960795 + 6072259 * 2 ^ 59
def prefixEnd_6072259 : Nat := 4983230072969 + 3 ^ 40 * 6072259 * 2
def baseEnd_6072259 : Nat := 3117987525589862992436695

theorem tailTrace_6072259 : CollatzResearch.WordTrace tailWord_6072259 prefixEnd_6072259 3117987525589862992436695 := by
  unfold tailWord_6072259
  simp only [CollatzResearch.WordTrace]
  refine ⟨221473480508250177117803831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147648987005500118078535887 221473480508250177117803831)
  ·
    refine ⟨332210220762375265676705747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221473480508250177117803831 332210220762375265676705747)
    ·
      refine ⟨498315331143562898515058621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332210220762375265676705747 498315331143562898515058621)
      ·
        refine ⟨186868249178836086943146983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498315331143562898515058621 186868249178836086943146983)
        ·
          refine ⟨280302373768254130414720475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186868249178836086943146983 280302373768254130414720475)
          ·
            refine ⟨420453560652381195622080713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280302373768254130414720475 420453560652381195622080713)
            ·
              refine ⟨315340170489285896716560535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420453560652381195622080713 315340170489285896716560535)
              ·
                refine ⟨473010255733928845074840803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315340170489285896716560535 473010255733928845074840803)
                ·
                  refine ⟨709515383600893267612261205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473010255733928845074840803 709515383600893267612261205)
                  ·
                    refine ⟨4157316700786483989915593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 709515383600893267612261205 4157316700786483989915593)
                    ·
                      refine ⟨3117987525589862992436695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157316700786483989915593 3117987525589862992436695)
                      ·
                        rfl

theorem cell23_6072259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_6072259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072259 prefixEnd_6072259 := by exact prefixLift 6072259
  have htrace : WordTrace (prefixWord ++ tailWord_6072259) baseStart_6072259 baseEnd_6072259 := by
    simpa [prefixWord, tailWord_6072259, baseEnd_6072259] using wordTrace_append hprefix tailTrace_6072259
  have hstable : (prefixWord ++ tailWord_6072259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072259).length < 2 ^ (prefixWord ++ tailWord_6072259).sum := by decide
  have hdescent : baseEnd_6072259 < baseStart_6072259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072284 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6072284 : Nat := 118140960795 + 6072284 * 2 ^ 59
def prefixEnd_6072284 : Nat := 4983230072969 + 3 ^ 40 * 6072284 * 2
def baseEnd_6072284 : Nat := 3118000362606225394624081

theorem tailTrace_6072284 : CollatzResearch.WordTrace tailWord_6072284 prefixEnd_6072284 3118000362606225394624081 := by
  unfold tailWord_6072284
  simp only [CollatzResearch.WordTrace]
  refine ⟨110737196166579803193731953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147649594888773070924975937 110737196166579803193731953)
  ·
    refine ⟨83052897124934852395298965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110737196166579803193731953 83052897124934852395298965)
    ·
      refine ⟨3893104552731321206029639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83052897124934852395298965 3893104552731321206029639)
      ·
        refine ⟨5839656829096981809044459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893104552731321206029639 5839656829096981809044459)
        ·
          refine ⟨8759485243645472713566689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5839656829096981809044459 8759485243645472713566689)
          ·
            refine ⟨6569613932734104535175017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8759485243645472713566689 6569613932734104535175017)
            ·
              refine ⟨4927210449550578401381263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6569613932734104535175017 4927210449550578401381263)
              ·
                refine ⟨7390815674325867602071895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927210449550578401381263 7390815674325867602071895)
                ·
                  refine ⟨11086223511488801403107843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7390815674325867602071895 11086223511488801403107843)
                  ·
                    refine ⟨16629335267233202104661765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11086223511488801403107843 16629335267233202104661765)
                    ·
                      refine ⟨3118000362606225394624081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16629335267233202104661765 3118000362606225394624081)
                      ·
                        rfl

theorem cell23_6072284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6072284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072284 prefixEnd_6072284 := by exact prefixLift 6072284
  have htrace : WordTrace (prefixWord ++ tailWord_6072284) baseStart_6072284 baseEnd_6072284 := by
    simpa [prefixWord, tailWord_6072284, baseEnd_6072284] using wordTrace_append hprefix tailTrace_6072284
  have hstable : (prefixWord ++ tailWord_6072284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072284).length < 2 ^ (prefixWord ++ tailWord_6072284).sum := by decide
  have hdescent : baseEnd_6072284 < baseStart_6072284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072323 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 2, 2, 2]
def baseStart_6072323 : Nat := 118140960795 + 6072323 * 2 ^ 59
def prefixEnd_6072323 : Nat := 4983230072969 + 3 ^ 40 * 6072323 * 2
def baseEnd_6072323 : Nat := 3118020388351750742036401

theorem tailTrace_6072323 : CollatzResearch.WordTrace tailWord_6072323 prefixEnd_6072323 3118020388351750742036401 := by
  unfold tailWord_6072323
  simp only [CollatzResearch.WordTrace]
  refine ⟨221475814780018316048133623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147650543186678877365422415 221475814780018316048133623)
  ·
    refine ⟨332213722170027474072200435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221475814780018316048133623 332213722170027474072200435)
    ·
      refine ⟨498320583255041211108300653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332213722170027474072200435 498320583255041211108300653)
      ·
        refine ⟨186870218720640454165612745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498320583255041211108300653 186870218720640454165612745)
        ·
          refine ⟨140152664040480340624209559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186870218720640454165612745 140152664040480340624209559)
          ·
            refine ⟨210228996060720510936314339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140152664040480340624209559 210228996060720510936314339)
            ·
              refine ⟨315343494091080766404471509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210228996060720510936314339 315343494091080766404471509)
              ·
                refine ⟨7390863142759705462604801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 315343494091080766404471509 7390863142759705462604801)
                ·
                  refine ⟨5543147357069779096953601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7390863142759705462604801 5543147357069779096953601)
                  ·
                    refine ⟨4157360517802334322715201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543147357069779096953601 4157360517802334322715201)
                    ·
                      refine ⟨3118020388351750742036401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157360517802334322715201 3118020388351750742036401)
                      ·
                        rfl

theorem cell23_6072323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_6072323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072323 prefixEnd_6072323 := by exact prefixLift 6072323
  have htrace : WordTrace (prefixWord ++ tailWord_6072323) baseStart_6072323 baseEnd_6072323 := by
    simpa [prefixWord, tailWord_6072323, baseEnd_6072323] using wordTrace_append hprefix tailTrace_6072323
  have hstable : (prefixWord ++ tailWord_6072323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072323).length < 2 ^ (prefixWord ++ tailWord_6072323).sum := by decide
  have hdescent : baseEnd_6072323 < baseStart_6072323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072339 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 3]
def baseStart_6072339 : Nat := 118140960795 + 6072339 * 2 ^ 59
def prefixEnd_6072339 : Nat := 4983230072969 + 3 ^ 40 * 6072339 * 2
def baseEnd_6072339 : Nat := 3118028604042222679436327

theorem tailTrace_6072339 : CollatzResearch.WordTrace tailWord_6072339 prefixEnd_6072339 3118028604042222679436327 := by
  unfold tailWord_6072339
  simp only [CollatzResearch.WordTrace]
  refine ⟨221476398347960350780716071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147650932231973567187144047 221476398347960350780716071)
  ·
    refine ⟨332214597521940526171074107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221476398347960350780716071 332214597521940526171074107)
    ·
      refine ⟨498321896282910789256611161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332214597521940526171074107 498321896282910789256611161)
      ·
        refine ⟨373741422212183091942458371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498321896282910789256611161 373741422212183091942458371)
        ·
          refine ⟨560612133318274637913687557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373741422212183091942458371 560612133318274637913687557)
          ·
            refine ⟨105114774997176494608816417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 560612133318274637913687557 105114774997176494608816417)
            ·
              refine ⟨78836081247882370956612313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105114774997176494608816417 78836081247882370956612313)
              ·
                refine ⟨59127060935911778217459235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78836081247882370956612313 59127060935911778217459235)
                ·
                  refine ⟨88690591403867667326188853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59127060935911778217459235 88690591403867667326188853)
                  ·
                    refine ⟨8314742944112593811830205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88690591403867667326188853 8314742944112593811830205)
                    ·
                      refine ⟨3118028604042222679436327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8314742944112593811830205 3118028604042222679436327)
                      ·
                        rfl

theorem cell23_6072339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_6072339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072339 prefixEnd_6072339 := by exact prefixLift 6072339
  have htrace : WordTrace (prefixWord ++ tailWord_6072339) baseStart_6072339 baseEnd_6072339 := by
    simpa [prefixWord, tailWord_6072339, baseEnd_6072339] using wordTrace_append hprefix tailTrace_6072339
  have hstable : (prefixWord ++ tailWord_6072339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072339).length < 2 ^ (prefixWord ++ tailWord_6072339).sum := by decide
  have hdescent : baseEnd_6072339 < baseStart_6072339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072369 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_6072369 : Nat := 118140960795 + 6072369 * 2 ^ 59
def prefixEnd_6072369 : Nat := 4983230072969 + 3 ^ 40 * 6072369 * 2
def baseEnd_6072369 : Nat := 3118044008461857562061189

theorem tailTrace_6072369 : CollatzResearch.WordTrace tailWord_6072369 prefixEnd_6072369 3118044008461857562061189 := by
  unfold tailWord_6072369
  simp only [CollatzResearch.WordTrace]
  refine ⟨221477492537851665904308161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147651661691901110602872107 221477492537851665904308161)
  ·
    refine ⟨166108119403388749428231121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221477492537851665904308161 166108119403388749428231121)
    ·
      refine ⟨124581089552541562071173341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166108119403388749428231121 124581089552541562071173341)
      ·
        refine ⟨46717908582203085776690003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124581089552541562071173341 46717908582203085776690003)
        ·
          refine ⟨70076862873304628665035005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46717908582203085776690003 70076862873304628665035005)
          ·
            refine ⟨26278823577489235749388127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70076862873304628665035005 26278823577489235749388127)
            ·
              refine ⟨39418235366233853624082191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26278823577489235749388127 39418235366233853624082191)
              ·
                refine ⟨59127353049350780436123287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39418235366233853624082191 59127353049350780436123287)
                ·
                  refine ⟨88691029574026170654184931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59127353049350780436123287 88691029574026170654184931)
                  ·
                    refine ⟨133036544361039255981277397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88691029574026170654184931 133036544361039255981277397)
                    ·
                      refine ⟨3118044008461857562061189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133036544361039255981277397 3118044008461857562061189)
                      ·
                        rfl

theorem cell23_6072369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_6072369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072369 prefixEnd_6072369 := by exact prefixLift 6072369
  have htrace : WordTrace (prefixWord ++ tailWord_6072369) baseStart_6072369 baseEnd_6072369 := by
    simpa [prefixWord, tailWord_6072369, baseEnd_6072369] using wordTrace_append hprefix tailTrace_6072369
  have hstable : (prefixWord ++ tailWord_6072369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072369).length < 2 ^ (prefixWord ++ tailWord_6072369).sum := by decide
  have hdescent : baseEnd_6072369 < baseStart_6072369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072396 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6072396 : Nat := 118140960795 + 6072396 * 2 ^ 59
def prefixEnd_6072396 : Nat := 4983230072969 + 3 ^ 40 * 6072396 * 2
def baseEnd_6072396 : Nat := 3118057872439528956423565

theorem tailTrace_6072396 : CollatzResearch.WordTrace tailWord_6072396 prefixEnd_6072396 3118057872439528956423565 := by
  unfold tailWord_6072396
  simp only [CollatzResearch.WordTrace]
  refine ⟨110739238654376924757770521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147652318205835899677027361 110739238654376924757770521)
  ·
    refine ⟨83054428990782693568327891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110739238654376924757770521 83054428990782693568327891)
    ·
      refine ⟨124581643486174040352491837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83054428990782693568327891 124581643486174040352491837)
      ·
        refine ⟨46718116307315265132184439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124581643486174040352491837 46718116307315265132184439)
        ·
          refine ⟨70077174460972897698276659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46718116307315265132184439 70077174460972897698276659)
          ·
            refine ⟨105115761691459346547414989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70077174460972897698276659 105115761691459346547414989)
            ·
              refine ⟨39418410634297254955280621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105115761691459346547414989 39418410634297254955280621)
              ·
                refine ⟨14781903987861470608230233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39418410634297254955280621 14781903987861470608230233)
                ·
                  refine ⟨11086427990896102956172675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14781903987861470608230233 11086427990896102956172675)
                  ·
                    refine ⟨16629641986344154434259013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11086427990896102956172675 16629641986344154434259013)
                    ·
                      refine ⟨3118057872439528956423565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16629641986344154434259013 3118057872439528956423565)
                      ·
                        rfl

theorem cell23_6072396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6072396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072396 prefixEnd_6072396 := by exact prefixLift 6072396
  have htrace : WordTrace (prefixWord ++ tailWord_6072396) baseStart_6072396 baseEnd_6072396 := by
    simpa [prefixWord, tailWord_6072396, baseEnd_6072396] using wordTrace_append hprefix tailTrace_6072396
  have hstable : (prefixWord ++ tailWord_6072396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072396).length < 2 ^ (prefixWord ++ tailWord_6072396).sum := by decide
  have hdescent : baseEnd_6072396 < baseStart_6072396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072409 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_6072409 : Nat := 118140960795 + 6072409 * 2 ^ 59
def prefixEnd_6072409 : Nat := 4983230072969 + 3 ^ 40 * 6072409 * 2
def baseEnd_6072409 : Nat := 3118064547688037405561005

theorem tailTrace_6072409 : CollatzResearch.WordTrace tailWord_6072409 prefixEnd_6072409 3118064547688037405561005 := by
  unfold tailWord_6072409
  simp only [CollatzResearch.WordTrace]
  refine ⟨221478951457706752735764281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147652634305137835157176187 221478951457706752735764281)
  ·
    refine ⟨166109213593280064551823211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221478951457706752735764281 166109213593280064551823211)
    ·
      refine ⟨249163820389920096827734817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166109213593280064551823211 249163820389920096827734817)
      ·
        refine ⟨186872865292440072620801113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249163820389920096827734817 186872865292440072620801113)
        ·
          refine ⟨140154648969330054465600835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186872865292440072620801113 140154648969330054465600835)
          ·
            refine ⟨210231973453995081698401253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140154648969330054465600835 210231973453995081698401253)
            ·
              refine ⟨39418495022624077818450235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210231973453995081698401253 39418495022624077818450235)
              ·
                refine ⟨59127742533936116727675353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39418495022624077818450235 59127742533936116727675353)
                ·
                  refine ⟨44345806900452087545756515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59127742533936116727675353 44345806900452087545756515)
                  ·
                    refine ⟨66518710350678131318634773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44345806900452087545756515 66518710350678131318634773)
                    ·
                      refine ⟨3118064547688037405561005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66518710350678131318634773 3118064547688037405561005)
                      ·
                        rfl

theorem cell23_6072409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_6072409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072409 prefixEnd_6072409 := by exact prefixLift 6072409
  have htrace : WordTrace (prefixWord ++ tailWord_6072409) baseStart_6072409 baseEnd_6072409 := by
    simpa [prefixWord, tailWord_6072409, baseEnd_6072409] using wordTrace_append hprefix tailTrace_6072409
  have hstable : (prefixWord ++ tailWord_6072409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072409).length < 2 ^ (prefixWord ++ tailWord_6072409).sum := by decide
  have hdescent : baseEnd_6072409 < baseStart_6072409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072419 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 8]
def baseStart_6072419 : Nat := 118140960795 + 6072419 * 2 ^ 59
def prefixEnd_6072419 : Nat := 4983230072969 + 3 ^ 40 * 6072419 * 2
def baseEnd_6072419 : Nat := 346452186943842485159551

theorem tailTrace_6072419 : CollatzResearch.WordTrace tailWord_6072419 prefixEnd_6072419 346452186943842485159551 := by
  unfold tailWord_6072419
  simp only [CollatzResearch.WordTrace]
  refine ⟨221479316187670524443628311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147652877458447016295752207 221479316187670524443628311)
  ·
    refine ⟨332218974281505786665442467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221479316187670524443628311 332218974281505786665442467)
    ·
      refine ⟨498328461422258679998163701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332218974281505786665442467 498328461422258679998163701)
      ·
        refine ⟨46718293258336751249827847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 498328461422258679998163701 46718293258336751249827847)
        ·
          refine ⟨70077439887505126874741771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46718293258336751249827847 70077439887505126874741771)
          ·
            refine ⟨105116159831257690312112657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70077439887505126874741771 105116159831257690312112657)
            ·
              refine ⟨78837119873443267734084493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105116159831257690312112657 78837119873443267734084493)
              ·
                refine ⟨29563919952541225400281685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78837119873443267734084493 29563919952541225400281685)
                ·
                  refine ⟨346452186943842485159551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29563919952541225400281685 346452186943842485159551)
                  ·
                    rfl

theorem cell23_6072419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 8].length) (baseStart_6072419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072419 prefixEnd_6072419 := by exact prefixLift 6072419
  have htrace : WordTrace (prefixWord ++ tailWord_6072419) baseStart_6072419 baseEnd_6072419 := by
    simpa [prefixWord, tailWord_6072419, baseEnd_6072419] using wordTrace_append hprefix tailTrace_6072419
  have hstable : (prefixWord ++ tailWord_6072419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072419).length < 2 ^ (prefixWord ++ tailWord_6072419).sum := by decide
  have hdescent : baseEnd_6072419 < baseStart_6072419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072459 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5]
def baseStart_6072459 : Nat := 118140960795 + 6072459 * 2 ^ 59
def prefixEnd_6072459 : Nat := 4983230072969 + 3 ^ 40 * 6072459 * 2
def baseEnd_6072459 : Nat := 3118090221720762209935775

theorem tailTrace_6072459 : CollatzResearch.WordTrace tailWord_6072459 prefixEnd_6072459 3118090221720762209935775 := by
  unfold tailWord_6072459
  simp only [CollatzResearch.WordTrace]
  refine ⟨221480775107525611275084431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147653850071683740850056287 221480775107525611275084431)
  ·
    refine ⟨332221162661288416912626647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221480775107525611275084431 332221162661288416912626647)
    ·
      refine ⟨498331743991932625368939971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332221162661288416912626647 498331743991932625368939971)
      ·
        refine ⟨747497615987898938053409957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498331743991932625368939971 747497615987898938053409957)
        ·
          refine ⟨140155802997731050885014367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 747497615987898938053409957 140155802997731050885014367)
          ·
            refine ⟨210233704496596576327521551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140155802997731050885014367 210233704496596576327521551)
            ·
              refine ⟨315350556744894864491282327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210233704496596576327521551 315350556744894864491282327)
              ·
                refine ⟨473025835117342296736923491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315350556744894864491282327 473025835117342296736923491)
                ·
                  refine ⟨709538752676013445105385237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473025835117342296736923491 709538752676013445105385237)
                  ·
                    refine ⟨33259629031688130239314933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 709538752676013445105385237 33259629031688130239314933)
                    ·
                      refine ⟨3118090221720762209935775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33259629031688130239314933 3118090221720762209935775)
                      ·
                        rfl

theorem cell23_6072459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_6072459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072459 prefixEnd_6072459 := by exact prefixLift 6072459
  have htrace : WordTrace (prefixWord ++ tailWord_6072459) baseStart_6072459 baseEnd_6072459 := by
    simpa [prefixWord, tailWord_6072459, baseEnd_6072459] using wordTrace_append hprefix tailTrace_6072459
  have hstable : (prefixWord ++ tailWord_6072459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072459).length < 2 ^ (prefixWord ++ tailWord_6072459).sum := by decide
  have hdescent : baseEnd_6072459 < baseStart_6072459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072473 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 2, 3, 2]
def baseStart_6072473 : Nat := 118140960795 + 6072473 * 2 ^ 59
def prefixEnd_6072473 : Nat := 4983230072969 + 3 ^ 40 * 6072473 * 2
def baseEnd_6072473 : Nat := 3118097410449925155160711

theorem tailTrace_6072473 : CollatzResearch.WordTrace tailWord_6072473 prefixEnd_6072473 3118097410449925155160711 := by
  unfold tailWord_6072473
  simp only [CollatzResearch.WordTrace]
  refine ⟨221481285729474891666094073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147654190486316594444062715 221481285729474891666094073)
  ·
    refine ⟨166110964297106168749570555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221481285729474891666094073 166110964297106168749570555)
    ·
      refine ⟨249166446445659253124355833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166110964297106168749570555 249166446445659253124355833)
      ·
        refine ⟨186874834834244439843266875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249166446445659253124355833 186874834834244439843266875)
        ·
          refine ⟨280312252251366659764900313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186874834834244439843266875 280312252251366659764900313)
          ·
            refine ⟨210234189188524994823675235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280312252251366659764900313 210234189188524994823675235)
            ·
              refine ⟨315351283782787492235512853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210234189188524994823675235 315351283782787492235512853)
              ·
                refine ⟨14782091427318163698539665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 315351283782787492235512853 14782091427318163698539665)
                ·
                  refine ⟨11086568570488622773904749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14782091427318163698539665 11086568570488622773904749)
                  ·
                    refine ⟨4157463213933233540214281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11086568570488622773904749 4157463213933233540214281)
                    ·
                      refine ⟨3118097410449925155160711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157463213933233540214281 3118097410449925155160711)
                      ·
                        rfl

theorem cell23_6072473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_6072473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072473 prefixEnd_6072473 := by exact prefixLift 6072473
  have htrace : WordTrace (prefixWord ++ tailWord_6072473) baseStart_6072473 baseEnd_6072473 := by
    simpa [prefixWord, tailWord_6072473, baseEnd_6072473] using wordTrace_append hprefix tailTrace_6072473
  have hstable : (prefixWord ++ tailWord_6072473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072473).length < 2 ^ (prefixWord ++ tailWord_6072473).sum := by decide
  have hdescent : baseEnd_6072473 < baseStart_6072473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072480 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 3, 1, 3]
def baseStart_6072480 : Nat := 118140960795 + 6072480 * 2 ^ 59
def prefixEnd_6072480 : Nat := 4983230072969 + 3 ^ 40 * 6072480 * 2
def baseEnd_6072480 : Nat := 3118101004814506627773179

theorem tailTrace_6072480 : CollatzResearch.WordTrace tailWord_6072480 prefixEnd_6072480 3118101004814506627773179 := by
  unfold tailWord_6072480
  simp only [CollatzResearch.WordTrace]
  refine ⟨110740770520224765930799447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147654360693633021241065929 110740770520224765930799447)
  ·
    refine ⟨166111155780337148896199171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110740770520224765930799447 166111155780337148896199171)
    ·
      refine ⟨249166733670505723344298757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166111155780337148896199171 249166733670505723344298757)
      ·
        refine ⟨46718762563219823127056017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249166733670505723344298757 46718762563219823127056017)
        ·
          refine ⟨35039071922414867345292013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46718762563219823127056017 35039071922414867345292013)
          ·
            refine ⟨13139651970905575254484505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35039071922414867345292013 13139651970905575254484505)
            ·
              refine ⟨9854738978179181440863379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13139651970905575254484505 9854738978179181440863379)
              ·
                refine ⟨14782108467268772161295069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9854738978179181440863379 14782108467268772161295069)
                ·
                  refine ⟨5543290675225789560485651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14782108467268772161295069 5543290675225789560485651)
                  ·
                    refine ⟨8314936012838684340728477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5543290675225789560485651 8314936012838684340728477)
                    ·
                      refine ⟨3118101004814506627773179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8314936012838684340728477 3118101004814506627773179)
                      ·
                        rfl

theorem cell23_6072480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_6072480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072480 prefixEnd_6072480 := by exact prefixLift 6072480
  have htrace : WordTrace (prefixWord ++ tailWord_6072480) baseStart_6072480 baseEnd_6072480 := by
    simpa [prefixWord, tailWord_6072480, baseEnd_6072480] using wordTrace_append hprefix tailTrace_6072480
  have hstable : (prefixWord ++ tailWord_6072480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072480).length < 2 ^ (prefixWord ++ tailWord_6072480).sum := by decide
  have hdescent : baseEnd_6072480 < baseStart_6072480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072496 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 8, 4]
def baseStart_6072496 : Nat := 118140960795 + 6072496 * 2 ^ 59
def prefixEnd_6072496 : Nat := 4983230072969 + 3 ^ 40 * 6072496 * 2
def baseEnd_6072496 : Nat := 1039369740168326188391035

theorem tailTrace_6072496 : CollatzResearch.WordTrace tailWord_6072496 prefixEnd_6072496 1039369740168326188391035 := by
  unfold tailWord_6072496
  simp only [CollatzResearch.WordTrace]
  refine ⟨110741062304195783297090671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147654749738927711062787561 110741062304195783297090671)
  ·
    refine ⟨166111593456293674945636007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110741062304195783297090671 166111593456293674945636007)
    ·
      refine ⟨249167390184440512418454011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166111593456293674945636007 249167390184440512418454011)
      ·
        refine ⟨373751085276660768627681017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249167390184440512418454011 373751085276660768627681017)
        ·
          refine ⟨280313313957495576470760763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373751085276660768627681017 280313313957495576470760763)
          ·
            refine ⟨420469970936243364706141145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280313313957495576470760763 420469970936243364706141145)
            ·
              refine ⟨315352478202182523529605859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420469970936243364706141145 315352478202182523529605859)
              ·
                refine ⟨473028717303273785294408789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315352478202182523529605859 473028717303273785294408789)
                ·
                  refine ⟨5543305280897739671418853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 473028717303273785294408789 5543305280897739671418853)
                  ·
                    refine ⟨1039369740168326188391035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5543305280897739671418853 1039369740168326188391035)
                    ·
                      rfl

theorem cell23_6072496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_6072496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072496 prefixEnd_6072496 := by exact prefixLift 6072496
  have htrace : WordTrace (prefixWord ++ tailWord_6072496) baseStart_6072496 baseEnd_6072496 := by
    simpa [prefixWord, tailWord_6072496, baseEnd_6072496] using wordTrace_append hprefix tailTrace_6072496
  have hstable : (prefixWord ++ tailWord_6072496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072496).length < 2 ^ (prefixWord ++ tailWord_6072496).sum := by decide
  have hdescent : baseEnd_6072496 < baseStart_6072496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072503 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_6072503 : Nat := 118140960795 + 6072503 * 2 ^ 59
def prefixEnd_6072503 : Nat := 4983230072969 + 3 ^ 40 * 6072503 * 2
def baseEnd_6072503 : Nat := 3118112814869560037785573

theorem tailTrace_6072503 : CollatzResearch.WordTrace tailWord_6072503 prefixEnd_6072503 3118112814869560037785573 := by
  unfold tailWord_6072503
  simp only [CollatzResearch.WordTrace]
  refine ⟨221482379919366206789686163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147654919946244137859790775 221482379919366206789686163)
  ·
    refine ⟨332223569879049310184529245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221482379919366206789686163 332223569879049310184529245)
    ·
      refine ⟨124583838704643491319198467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332223569879049310184529245 124583838704643491319198467)
      ·
        refine ⟨186875758056965236978797701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124583838704643491319198467 186875758056965236978797701)
        ·
          refine ⟨35039204635680981933524569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186875758056965236978797701 35039204635680981933524569)
          ·
            refine ⟨26279403476760736450143427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35039204635680981933524569 26279403476760736450143427)
            ·
              refine ⟨39419105215141104675215141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26279403476760736450143427 39419105215141104675215141)
              ·
                refine ⟨7391082227838957126602839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39419105215141104675215141 7391082227838957126602839)
                ·
                  refine ⟨11086623341758435689904259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391082227838957126602839 11086623341758435689904259)
                  ·
                    refine ⟨16629935012637653534856389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11086623341758435689904259 16629935012637653534856389)
                    ·
                      refine ⟨3118112814869560037785573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16629935012637653534856389 3118112814869560037785573)
                      ·
                        rfl

theorem cell23_6072503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_6072503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072503 prefixEnd_6072503 := by exact prefixLift 6072503
  have htrace : WordTrace (prefixWord ++ tailWord_6072503) baseStart_6072503 baseEnd_6072503 := by
    simpa [prefixWord, tailWord_6072503, baseEnd_6072503] using wordTrace_append hprefix tailTrace_6072503
  have hstable : (prefixWord ++ tailWord_6072503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072503).length < 2 ^ (prefixWord ++ tailWord_6072503).sum := by decide
  have hdescent : baseEnd_6072503 < baseStart_6072503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072523 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 3]
def baseStart_6072523 : Nat := 118140960795 + 6072523 * 2 ^ 59
def prefixEnd_6072523 : Nat := 4983230072969 + 3 ^ 40 * 6072523 * 2
def baseEnd_6072523 : Nat := 3118123084482649959535481

theorem tailTrace_6072523 : CollatzResearch.WordTrace tailWord_6072523 prefixEnd_6072523 3118123084482649959535481 := by
  unfold tailWord_6072523
  simp only [CollatzResearch.WordTrace]
  refine ⟨221483109379293750205414223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147655406252862500136942815 221483109379293750205414223)
  ·
    refine ⟨332224664068940625308121335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221483109379293750205414223 332224664068940625308121335)
    ·
      refine ⟨498336996103410937962182003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332224664068940625308121335 498336996103410937962182003)
      ·
        refine ⟨747505494155116406943273005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498336996103410937962182003 747505494155116406943273005)
        ·
          refine ⟨280314560308168652603727377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747505494155116406943273005 280314560308168652603727377)
          ·
            refine ⟨210235920231126489452795533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280314560308168652603727377 210235920231126489452795533)
            ·
              refine ⟨78838470086672433544798325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210235920231126489452795533 78838470086672433544798325)
              ·
                refine ⟨7391106570625540644824843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78838470086672433544798325 7391106570625540644824843)
                ·
                  refine ⟨11086659855938310967237265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391106570625540644824843 11086659855938310967237265)
                  ·
                    refine ⟨8314994891953733225427949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11086659855938310967237265 8314994891953733225427949)
                    ·
                      refine ⟨3118123084482649959535481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8314994891953733225427949 3118123084482649959535481)
                      ·
                        rfl

theorem cell23_6072523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 2, 3].length) (baseStart_6072523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072523 prefixEnd_6072523 := by exact prefixLift 6072523
  have htrace : WordTrace (prefixWord ++ tailWord_6072523) baseStart_6072523 baseEnd_6072523 := by
    simpa [prefixWord, tailWord_6072523, baseEnd_6072523] using wordTrace_append hprefix tailTrace_6072523
  have hstable : (prefixWord ++ tailWord_6072523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072523).length < 2 ^ (prefixWord ++ tailWord_6072523).sum := by decide
  have hdescent : baseEnd_6072523 < baseStart_6072523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072526 : List Nat := [4, 1, 1, 1, 4, 1, 11]
def baseStart_6072526 : Nat := 118140960795 + 6072526 * 2 ^ 59
def prefixEnd_6072526 : Nat := 4983230072969 + 3 ^ 40 * 6072526 * 2
def baseEnd_6072526 : Nat := 38495365739810042565407

theorem tailTrace_6072526 : CollatzResearch.WordTrace tailWord_6072526 prefixEnd_6072526 38495365739810042565407 := by
  unfold tailWord_6072526
  simp only [CollatzResearch.WordTrace]
  refine ⟨27685402349785360214721679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147655479198855254478515621 27685402349785360214721679)
  ·
    refine ⟨41528103524678040322082519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27685402349785360214721679 41528103524678040322082519)
    ·
      refine ⟨62292155287017060483123779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41528103524678040322082519 62292155287017060483123779)
      ·
        refine ⟨93438232930525590724685669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62292155287017060483123779 93438232930525590724685669)
        ·
          refine ⟨17519668674473548260878563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93438232930525590724685669 17519668674473548260878563)
          ·
            refine ⟨26279503011710322391317845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17519668674473548260878563 26279503011710322391317845)
            ·
              refine ⟨38495365739810042565407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26279503011710322391317845 38495365739810042565407)
              ·
                rfl

theorem cell23_6072526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 11].length) (baseStart_6072526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072526 prefixEnd_6072526 := by exact prefixLift 6072526
  have htrace : WordTrace (prefixWord ++ tailWord_6072526) baseStart_6072526 baseEnd_6072526 := by
    simpa [prefixWord, tailWord_6072526, baseEnd_6072526] using wordTrace_append hprefix tailTrace_6072526
  have hstable : (prefixWord ++ tailWord_6072526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072526).length < 2 ^ (prefixWord ++ tailWord_6072526).sum := by decide
  have hdescent : baseEnd_6072526 < baseStart_6072526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072537 : List Nat := [1, 2, 1, 2, 3, 1, 2, 6, 1, 2, 2]
def baseStart_6072537 : Nat := 118140960795 + 6072537 * 2 ^ 59
def prefixEnd_6072537 : Nat := 4983230072969 + 3 ^ 40 * 6072537 * 2
def baseEnd_6072537 : Nat := 3118130273211812904760417

theorem tailTrace_6072537 : CollatzResearch.WordTrace tailWord_6072537 prefixEnd_6072537 3118130273211812904760417 := by
  unfold tailWord_6072537
  simp only [CollatzResearch.WordTrace]
  refine ⟨221483620001243030596423865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147655746667495353730949243 221483620001243030596423865)
  ·
    refine ⟨166112715000932272947317899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221483620001243030596423865 166112715000932272947317899)
    ·
      refine ⟨249169072501398409420976849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166112715000932272947317899 249169072501398409420976849)
      ·
        refine ⟨186876804376048807065732637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249169072501398409420976849 186876804376048807065732637)
        ·
          refine ⟨70078801641018302649649739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186876804376048807065732637 70078801641018302649649739)
          ·
            refine ⟨105118202461527453974474609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70078801641018302649649739 105118202461527453974474609)
            ·
              refine ⟨78838651846145590480855957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105118202461527453974474609 78838651846145590480855957)
              ·
                refine ⟨3695561805288074553790123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78838651846145590480855957 3695561805288074553790123)
                ·
                  refine ⟨5543342707932111830685185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695561805288074553790123 5543342707932111830685185)
                  ·
                    refine ⟨4157507030949083873013889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543342707932111830685185 4157507030949083873013889)
                    ·
                      refine ⟨3118130273211812904760417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157507030949083873013889 3118130273211812904760417)
                      ·
                        rfl

theorem cell23_6072537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_6072537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072537 prefixEnd_6072537 := by exact prefixLift 6072537
  have htrace : WordTrace (prefixWord ++ tailWord_6072537) baseStart_6072537 baseEnd_6072537 := by
    simpa [prefixWord, tailWord_6072537, baseEnd_6072537] using wordTrace_append hprefix tailTrace_6072537
  have hstable : (prefixWord ++ tailWord_6072537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072537).length < 2 ^ (prefixWord ++ tailWord_6072537).sum := by decide
  have hdescent : baseEnd_6072537 < baseStart_6072537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072547 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 2, 4]
def baseStart_6072547 : Nat := 118140960795 + 6072547 * 2 ^ 59
def prefixEnd_6072547 : Nat := 4983230072969 + 3 ^ 40 * 6072547 * 2
def baseEnd_6072547 : Nat := 1039378469339452621878457

theorem tailTrace_6072547 : CollatzResearch.WordTrace tailWord_6072547 prefixEnd_6072547 1039378469339452621878457 := by
  unfold tailWord_6072547
  simp only [CollatzResearch.WordTrace]
  refine ⟨221483984731206802304287895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147655989820804534869525263 221483984731206802304287895)
  ·
    refine ⟨332225977096810203456431843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221483984731206802304287895 332225977096810203456431843)
    ·
      refine ⟨498338965645215305184647765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332225977096810203456431843 498338965645215305184647765)
      ·
        refine ⟨5839909753654866857632591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 498338965645215305184647765 5839909753654866857632591)
        ·
          refine ⟨8759864630482300286448887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5839909753654866857632591 8759864630482300286448887)
          ·
            refine ⟨13139796945723450429673331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8759864630482300286448887 13139796945723450429673331)
            ·
              refine ⟨19709695418585175644509997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13139796945723450429673331 19709695418585175644509997)
              ·
                refine ⟨7391135781969440866691249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19709695418585175644509997 7391135781969440866691249)
                ·
                  refine ⟨5543351836477080650018437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7391135781969440866691249 5543351836477080650018437)
                  ·
                    refine ⟨1039378469339452621878457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5543351836477080650018437 1039378469339452621878457)
                    ·
                      rfl

theorem cell23_6072547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 4].length) (baseStart_6072547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072547 prefixEnd_6072547 := by exact prefixLift 6072547
  have htrace : WordTrace (prefixWord ++ tailWord_6072547) baseStart_6072547 baseEnd_6072547 := by
    simpa [prefixWord, tailWord_6072547, baseEnd_6072547] using wordTrace_append hprefix tailTrace_6072547
  have hstable : (prefixWord ++ tailWord_6072547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072547).length < 2 ^ (prefixWord ++ tailWord_6072547).sum := by decide
  have hdescent : baseEnd_6072547 < baseStart_6072547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072643 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 3]
def baseStart_6072643 : Nat := 118140960795 + 6072643 * 2 ^ 59
def prefixEnd_6072643 : Nat := 4983230072969 + 3 ^ 40 * 6072643 * 2
def baseEnd_6072643 : Nat := 3118184702161189490034929

theorem tailTrace_6072643 : CollatzResearch.WordTrace tailWord_6072643 prefixEnd_6072643 3118184702161189490034929 := by
  unfold tailWord_6072643
  simp only [CollatzResearch.WordTrace]
  refine ⟨221487486138859010699782583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147658324092572673799855055 221487486138859010699782583)
  ·
    refine ⟨332231229208288516049673875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221487486138859010699782583 332231229208288516049673875)
    ·
      refine ⟨498346843812432774074510813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332231229208288516049673875 498346843812432774074510813)
      ·
        refine ⟨186880066429662290277941555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498346843812432774074510813 186880066429662290277941555)
        ·
          refine ⟨280320099644493435416912333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186880066429662290277941555 280320099644493435416912333)
          ·
            refine ⟨105120037366685038281342125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280320099644493435416912333 105120037366685038281342125)
            ·
              refine ⟨39420014012506889355503297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105120037366685038281342125 39420014012506889355503297)
              ·
                refine ⟨29565010509380167016627473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39420014012506889355503297 29565010509380167016627473)
                ·
                  refine ⟨22173757882035125262470605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29565010509380167016627473 22173757882035125262470605)
                  ·
                    refine ⟨8315159205763171973426477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22173757882035125262470605 8315159205763171973426477)
                    ·
                      refine ⟨3118184702161189490034929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8315159205763171973426477 3118184702161189490034929)
                      ·
                        rfl

theorem cell23_6072643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_6072643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072643 prefixEnd_6072643 := by exact prefixLift 6072643
  have htrace : WordTrace (prefixWord ++ tailWord_6072643) baseStart_6072643 baseEnd_6072643 := by
    simpa [prefixWord, tailWord_6072643, baseEnd_6072643] using wordTrace_append hprefix tailTrace_6072643
  have hstable : (prefixWord ++ tailWord_6072643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072643).length < 2 ^ (prefixWord ++ tailWord_6072643).sum := by decide
  have hdescent : baseEnd_6072643 < baseStart_6072643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072660 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_6072660 : Nat := 118140960795 + 6072660 * 2 ^ 59
def prefixEnd_6072660 : Nat := 4983230072969 + 3 ^ 40 * 6072660 * 2
def baseEnd_6072660 : Nat := 3118193431332315923522351

theorem tailTrace_6072660 : CollatzResearch.WordTrace tailWord_6072660 prefixEnd_6072660 3118193431332315923522351 := by
  unfold tailWord_6072660
  simp only [CollatzResearch.WordTrace]
  refine ⟨110744053089898711301575717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147658737453198281735434289 110744053089898711301575717)
  ·
    refine ⟨20764509954356008369045447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110744053089898711301575717 20764509954356008369045447)
    ·
      refine ⟨31146764931534012553568171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20764509954356008369045447 31146764931534012553568171)
      ·
        refine ⟨46720147397301018830352257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31146764931534012553568171 46720147397301018830352257)
        ·
          refine ⟨35040110547975764122764193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46720147397301018830352257 35040110547975764122764193)
          ·
            refine ⟨26280082910981823092073145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35040110547975764122764193 26280082910981823092073145)
            ·
              refine ⟨19710062183236367319054859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26280082910981823092073145 19710062183236367319054859)
              ·
                refine ⟨29565093274854550978582289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19710062183236367319054859 29565093274854550978582289)
                ·
                  refine ⟨22173819956140913233936717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29565093274854550978582289 22173819956140913233936717)
                  ·
                    refine ⟨8315182483552842462726269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22173819956140913233936717 8315182483552842462726269)
                    ·
                      refine ⟨3118193431332315923522351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8315182483552842462726269 3118193431332315923522351)
                      ·
                        rfl

theorem cell23_6072660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_6072660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072660 prefixEnd_6072660 := by exact prefixLift 6072660
  have htrace : WordTrace (prefixWord ++ tailWord_6072660) baseStart_6072660 baseEnd_6072660 := by
    simpa [prefixWord, tailWord_6072660, baseEnd_6072660] using wordTrace_append hprefix tailTrace_6072660
  have hstable : (prefixWord ++ tailWord_6072660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072660).length < 2 ^ (prefixWord ++ tailWord_6072660).sum := by decide
  have hdescent : baseEnd_6072660 < baseStart_6072660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072661 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_6072661 : Nat := 118140960795 + 6072661 * 2 ^ 59
def prefixEnd_6072661 : Nat := 4983230072969 + 3 ^ 40 * 6072661 * 2
def baseEnd_6072661 : Nat := 3118193944812970419609847

theorem tailTrace_6072661 : CollatzResearch.WordTrace tailWord_6072661 prefixEnd_6072661 3118193944812970419609847 := by
  unfold tailWord_6072661
  simp only [CollatzResearch.WordTrace]
  refine ⟨221488142652793799773937837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147658761768529199849291891 221488142652793799773937837)
  ·
    refine ⟨83058053494797674915226689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221488142652793799773937837 83058053494797674915226689)
    ·
      refine ⟨62293540121098256186420017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83058053494797674915226689 62293540121098256186420017)
      ·
        refine ⟨46720155090823692139815013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62293540121098256186420017 46720155090823692139815013)
        ·
          refine ⟨8760029079529442276215315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46720155090823692139815013 8760029079529442276215315)
          ·
            refine ⟨13140043619294163414322973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760029079529442276215315 13140043619294163414322973)
            ·
              refine ⟨4927516357235311280371115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13140043619294163414322973 4927516357235311280371115)
              ·
                refine ⟨7391274535852966920556673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927516357235311280371115 7391274535852966920556673)
                ·
                  refine ⟨5543455901889725190417505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7391274535852966920556673 5543455901889725190417505)
                  ·
                    refine ⟨4157591926417293892813129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543455901889725190417505 4157591926417293892813129)
                    ·
                      refine ⟨3118193944812970419609847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157591926417293892813129 3118193944812970419609847)
                      ·
                        rfl

theorem cell23_6072661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_6072661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072661 prefixEnd_6072661 := by exact prefixLift 6072661
  have htrace : WordTrace (prefixWord ++ tailWord_6072661) baseStart_6072661 baseEnd_6072661 := by
    simpa [prefixWord, tailWord_6072661, baseEnd_6072661] using wordTrace_append hprefix tailTrace_6072661
  have hstable : (prefixWord ++ tailWord_6072661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072661).length < 2 ^ (prefixWord ++ tailWord_6072661).sum := by decide
  have hdescent : baseEnd_6072661 < baseStart_6072661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072684 : List Nat := [2, 2, 1, 1, 7, 1, 1, 3, 5]
def baseStart_6072684 : Nat := 118140960795 + 6072684 * 2 ^ 59
def prefixEnd_6072684 : Nat := 4983230072969 + 3 ^ 40 * 6072684 * 2
def baseEnd_6072684 : Nat := 346467306096447092180249

theorem tailTrace_6072684 : CollatzResearch.WordTrace tailWord_6072684 prefixEnd_6072684 346467306096447092180249 := by
  unfold tailWord_6072684
  simp only [CollatzResearch.WordTrace]
  refine ⟨110744490765855237351012553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147659321021140316468016737 110744490765855237351012553)
  ·
    refine ⟨83058368074391428013259415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110744490765855237351012553 83058368074391428013259415)
    ·
      refine ⟨124587552111587142019889123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83058368074391428013259415 124587552111587142019889123)
      ·
        refine ⟨186881328167380713029833685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124587552111587142019889123 186881328167380713029833685)
        ·
          refine ⟨4380031128922985461636727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 186881328167380713029833685 4380031128922985461636727)
          ·
            refine ⟨6570046693384478192455091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380031128922985461636727 6570046693384478192455091)
            ·
              refine ⟨9855070040076717288682637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570046693384478192455091 9855070040076717288682637)
              ·
                refine ⟨3695651265028768983255989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9855070040076717288682637 3695651265028768983255989)
                ·
                  refine ⟨346467306096447092180249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3695651265028768983255989 346467306096447092180249)
                  ·
                    rfl

theorem cell23_6072684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_6072684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072684 prefixEnd_6072684 := by exact prefixLift 6072684
  have htrace : WordTrace (prefixWord ++ tailWord_6072684) baseStart_6072684 baseEnd_6072684 := by
    simpa [prefixWord, tailWord_6072684, baseEnd_6072684] using wordTrace_append hprefix tailTrace_6072684
  have hstable : (prefixWord ++ tailWord_6072684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072684).length < 2 ^ (prefixWord ++ tailWord_6072684).sum := by decide
  have hdescent : baseEnd_6072684 < baseStart_6072684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072700 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_6072700 : Nat := 118140960795 + 6072700 * 2 ^ 59
def prefixEnd_6072700 : Nat := 4983230072969 + 3 ^ 40 * 6072700 * 2
def baseEnd_6072700 : Nat := 3118213970558495767022167

theorem tailTrace_6072700 : CollatzResearch.WordTrace tailWord_6072700 prefixEnd_6072700 3118213970558495767022167 := by
  unfold tailWord_6072700
  simp only [CollatzResearch.WordTrace]
  refine ⟨110744782549826254717303777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147659710066435006289738369 110744782549826254717303777)
  ·
    refine ⟨83058586912369691037977833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110744782549826254717303777 83058586912369691037977833)
    ·
      refine ⟨62293940184277268278483375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83058586912369691037977833 62293940184277268278483375)
      ·
        refine ⟨93440910276415902417725063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62293940184277268278483375 93440910276415902417725063)
        ·
          refine ⟨140161365414623853626587595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93440910276415902417725063 140161365414623853626587595)
          ·
            refine ⟨210242048121935780439881393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140161365414623853626587595 210242048121935780439881393)
            ·
              refine ⟨157681536091451835329911045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210242048121935780439881393 157681536091451835329911045)
              ·
                refine ⟨29565288017147219124358321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157681536091451835329911045 29565288017147219124358321)
                ·
                  refine ⟨22173966012860414343268741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29565288017147219124358321 22173966012860414343268741)
                  ·
                    refine ⟨4157618627411327689362889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22173966012860414343268741 4157618627411327689362889)
                    ·
                      refine ⟨3118213970558495767022167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157618627411327689362889 3118213970558495767022167)
                      ·
                        rfl

theorem cell23_6072700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_6072700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072700 prefixEnd_6072700 := by exact prefixLift 6072700
  have htrace : WordTrace (prefixWord ++ tailWord_6072700) baseStart_6072700 baseEnd_6072700 := by
    simpa [prefixWord, tailWord_6072700, baseEnd_6072700] using wordTrace_append hprefix tailTrace_6072700
  have hstable : (prefixWord ++ tailWord_6072700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072700).length < 2 ^ (prefixWord ++ tailWord_6072700).sum := by decide
  have hdescent : baseEnd_6072700 < baseStart_6072700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072734 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6072734 : Nat := 118140960795 + 6072734 * 2 ^ 59
def prefixEnd_6072734 : Nat := 4983230072969 + 3 ^ 40 * 6072734 * 2
def baseEnd_6072734 : Nat := 3118231428900748633997011

theorem tailTrace_6072734 : CollatzResearch.WordTrace tailWord_6072734 prefixEnd_6072734 3118231428900748633997011 := by
  unfold tailWord_6072734
  simp only [CollatzResearch.WordTrace]
  refine ⟨27686350647691166655168157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147660536787686222160896837 27686350647691166655168157)
  ·
    refine ⟨10382381492884187495688059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27686350647691166655168157 10382381492884187495688059)
    ·
      refine ⟨15573572239326281243532089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10382381492884187495688059 15573572239326281243532089)
      ·
        refine ⟨11680179179494710932649067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15573572239326281243532089 11680179179494710932649067)
        ·
          refine ⟨17520268769242066398973601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11680179179494710932649067 17520268769242066398973601)
          ·
            refine ⟨13140201576931549799230201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17520268769242066398973601 13140201576931549799230201)
            ·
              refine ⟨9855151182698662349422651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13140201576931549799230201 9855151182698662349422651)
              ·
                refine ⟨14782726774047993524133977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9855151182698662349422651 14782726774047993524133977)
                ·
                  refine ⟨11087045080535995143100483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14782726774047993524133977 11087045080535995143100483)
                  ·
                    refine ⟨16630567620803992714650725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11087045080535995143100483 16630567620803992714650725)
                    ·
                      refine ⟨3118231428900748633997011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16630567620803992714650725 3118231428900748633997011)
                      ·
                        rfl

theorem cell23_6072734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6072734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072734 prefixEnd_6072734 := by exact prefixLift 6072734
  have htrace : WordTrace (prefixWord ++ tailWord_6072734) baseStart_6072734 baseEnd_6072734 := by
    simpa [prefixWord, tailWord_6072734, baseEnd_6072734] using wordTrace_append hprefix tailTrace_6072734
  have hstable : (prefixWord ++ tailWord_6072734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072734).length < 2 ^ (prefixWord ++ tailWord_6072734).sum := by decide
  have hdescent : baseEnd_6072734 < baseStart_6072734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072757 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 6]
def baseStart_6072757 : Nat := 118140960795 + 6072757 * 2 ^ 59
def prefixEnd_6072757 : Nat := 4983230072969 + 3 ^ 40 * 6072757 * 2
def baseEnd_6072757 : Nat := 346471470995089116001045

theorem tailTrace_6072757 : CollatzResearch.WordTrace tailWord_6072757 prefixEnd_6072757 346471470995089116001045 := by
  unfold tailWord_6072757
  simp only [CollatzResearch.WordTrace]
  refine ⟨221491644060446008169432525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147661096040297338779621683 221491644060446008169432525)
  ·
    refine ⟨83059366522667253063537197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221491644060446008169432525 83059366522667253063537197)
    ·
      refine ⟨31147262446000219898826449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83059366522667253063537197 31147262446000219898826449)
      ·
        refine ⟨23360446834500164924119837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31147262446000219898826449 23360446834500164924119837)
        ·
          refine ⟨8760167562937561846544939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23360446834500164924119837 8760167562937561846544939)
          ·
            refine ⟨13140251344406342769817409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760167562937561846544939 13140251344406342769817409)
            ·
              refine ⟨9855188508304757077363057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13140251344406342769817409 9855188508304757077363057)
              ·
                refine ⟨7391391381228567808022293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9855188508304757077363057 7391391381228567808022293)
                ·
                  refine ⟨346471470995089116001045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7391391381228567808022293 346471470995089116001045)
                  ·
                    rfl

theorem cell23_6072757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_6072757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072757 prefixEnd_6072757 := by exact prefixLift 6072757
  have htrace : WordTrace (prefixWord ++ tailWord_6072757) baseStart_6072757 baseEnd_6072757 := by
    simpa [prefixWord, tailWord_6072757, baseEnd_6072757] using wordTrace_append hprefix tailTrace_6072757
  have hstable : (prefixWord ++ tailWord_6072757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072757).length < 2 ^ (prefixWord ++ tailWord_6072757).sum := by decide
  have hdescent : baseEnd_6072757 < baseStart_6072757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072760 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 3, 5, 2]
def baseStart_6072760 : Nat := 118140960795 + 6072760 * 2 ^ 59
def prefixEnd_6072760 : Nat := 4983230072969 + 3 ^ 40 * 6072760 * 2
def baseEnd_6072760 : Nat := 3118244779397765532271891

theorem tailTrace_6072760 : CollatzResearch.WordTrace tailWord_6072760 prefixEnd_6072760 3118244779397765532271891 := by
  unfold tailWord_6072760
  simp only [CollatzResearch.WordTrace]
  refine ⟨110745876739717569840895867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147661168986290093121194489 110745876739717569840895867)
  ·
    refine ⟨166118815109576354761343801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110745876739717569840895867 166118815109576354761343801)
    ·
      refine ⟨124589111332182266071007851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166118815109576354761343801 124589111332182266071007851)
      ·
        refine ⟨186883666998273399106511777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124589111332182266071007851 186883666998273399106511777)
        ·
          refine ⟨140162750248705049329883833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186883666998273399106511777 140162750248705049329883833)
          ·
            refine ⟨105122062686528786997412875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140162750248705049329883833 105122062686528786997412875)
            ·
              refine ⟨157683094029793180496119313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105122062686528786997412875 157683094029793180496119313)
              ·
                refine ⟨118262320522344885372089485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157683094029793180496119313 118262320522344885372089485)
                ·
                  refine ⟨44348370195879332014533557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118262320522344885372089485 44348370195879332014533557)
                  ·
                    refine ⟨4157659705863687376362521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44348370195879332014533557 4157659705863687376362521)
                    ·
                      refine ⟨3118244779397765532271891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157659705863687376362521 3118244779397765532271891)
                      ·
                        rfl

theorem cell23_6072760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_6072760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072760 prefixEnd_6072760 := by exact prefixLift 6072760
  have htrace : WordTrace (prefixWord ++ tailWord_6072760) baseStart_6072760 baseEnd_6072760 := by
    simpa [prefixWord, tailWord_6072760, baseEnd_6072760] using wordTrace_append hprefix tailTrace_6072760
  have hstable : (prefixWord ++ tailWord_6072760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072760).length < 2 ^ (prefixWord ++ tailWord_6072760).sum := by decide
  have hdescent : baseEnd_6072760 < baseStart_6072760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072761 : List Nat := [1, 2, 1, 4, 3, 3, 2, 2, 1, 4]
def baseStart_6072761 : Nat := 118140960795 + 6072761 * 2 ^ 59
def prefixEnd_6072761 : Nat := 4983230072969 + 3 ^ 40 * 6072761 * 2
def baseEnd_6072761 : Nat := 1039415097626140009453129

theorem tailTrace_6072761 : CollatzResearch.WordTrace tailWord_6072761 prefixEnd_6072761 1039415097626140009453129 := by
  unfold tailWord_6072761
  simp only [CollatzResearch.WordTrace]
  refine ⟨221491789952431516852578137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147661193301621011235052091 221491789952431516852578137)
  ·
    refine ⟨166118842464323637639433603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221491789952431516852578137 166118842464323637639433603)
    ·
      refine ⟨249178263696485456459150405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166118842464323637639433603 249178263696485456459150405)
      ·
        refine ⟨46720924443091023086090701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249178263696485456459150405 46720924443091023086090701)
        ·
          refine ⟨17520346666159133657284013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46720924443091023086090701 17520346666159133657284013)
          ·
            refine ⟨6570129999809675121481505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17520346666159133657284013 6570129999809675121481505)
            ·
              refine ⟨4927597499857256341111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6570129999809675121481505 4927597499857256341111129)
              ·
                refine ⟨3695698124892942255833347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4927597499857256341111129 3695698124892942255833347)
                ·
                  refine ⟨5543547187339413383750021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695698124892942255833347 5543547187339413383750021)
                  ·
                    refine ⟨1039415097626140009453129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5543547187339413383750021 1039415097626140009453129)
                    ·
                      rfl

theorem cell23_6072761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 4].length) (baseStart_6072761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072761 prefixEnd_6072761 := by exact prefixLift 6072761
  have htrace : WordTrace (prefixWord ++ tailWord_6072761) baseStart_6072761 baseEnd_6072761 := by
    simpa [prefixWord, tailWord_6072761, baseEnd_6072761] using wordTrace_append hprefix tailTrace_6072761
  have hstable : (prefixWord ++ tailWord_6072761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072761).length < 2 ^ (prefixWord ++ tailWord_6072761).sum := by decide
  have hdescent : baseEnd_6072761 < baseStart_6072761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072800 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 4, 4]
def baseStart_6072800 : Nat := 118140960795 + 6072800 * 2 ^ 59
def prefixEnd_6072800 : Nat := 4983230072969 + 3 ^ 40 * 6072800 * 2
def baseEnd_6072800 : Nat := 1039421772874648458590569

theorem tailTrace_6072800 : CollatzResearch.WordTrace tailWord_6072800 prefixEnd_6072800 1039421772874648458590569 := by
  unfold tailWord_6072800
  simp only [CollatzResearch.WordTrace]
  refine ⟨110746606199645113256623927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147662141599526817675498569 110746606199645113256623927)
  ·
    refine ⟨166119909299467669884935891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110746606199645113256623927 166119909299467669884935891)
    ·
      refine ⟨249179863949201504827403837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166119909299467669884935891 249179863949201504827403837)
      ·
        refine ⟨93442448980950564310276439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249179863949201504827403837 93442448980950564310276439)
        ·
          refine ⟨140163673471425846465414659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93442448980950564310276439 140163673471425846465414659)
          ·
            refine ⟨210245510207138769698121989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140163673471425846465414659 210245510207138769698121989)
            ·
              refine ⟨39421033163838519318397873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210245510207138769698121989 39421033163838519318397873)
              ·
                refine ⟨29565774872878889488798405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39421033163838519318397873 29565774872878889488798405)
                ·
                  refine ⟨5543582788664791779149701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29565774872878889488798405 5543582788664791779149701)
                  ·
                    refine ⟨1039421772874648458590569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5543582788664791779149701 1039421772874648458590569)
                    ·
                      rfl

theorem cell23_6072800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_6072800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072800 prefixEnd_6072800 := by exact prefixLift 6072800
  have htrace : WordTrace (prefixWord ++ tailWord_6072800) baseStart_6072800 baseEnd_6072800 := by
    simpa [prefixWord, tailWord_6072800, baseEnd_6072800] using wordTrace_append hprefix tailTrace_6072800
  have hstable : (prefixWord ++ tailWord_6072800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072800).length < 2 ^ (prefixWord ++ tailWord_6072800).sum := by decide
  have hdescent : baseEnd_6072800 < baseStart_6072800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072807 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_6072807 : Nat := 118140960795 + 6072807 * 2 ^ 59
def prefixEnd_6072807 : Nat := 4983230072969 + 3 ^ 40 * 6072807 * 2
def baseEnd_6072807 : Nat := 3118268912988526848384175

theorem tailTrace_6072807 : CollatzResearch.WordTrace tailWord_6072807 prefixEnd_6072807 3118268912988526848384175 := by
  unfold tailWord_6072807
  simp only [CollatzResearch.WordTrace]
  refine ⟨221493467710264866708752675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147662311806843244472501783 221493467710264866708752675)
  ·
    refine ⟨332240201565397300063129013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221493467710264866708752675 332240201565397300063129013)
    ·
      refine ⟨31147518896755996880918345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 332240201565397300063129013 31147518896755996880918345)
      ·
        refine ⟨23360639172566997660688759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31147518896755996880918345 23360639172566997660688759)
        ·
          refine ⟨35040958758850496491033139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23360639172566997660688759 35040958758850496491033139)
          ·
            refine ⟨52561438138275744736549709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35040958758850496491033139 52561438138275744736549709)
            ·
              refine ⟨19710539301853404276206141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52561438138275744736549709 19710539301853404276206141)
              ·
                refine ⟨7391452238195026603577303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19710539301853404276206141 7391452238195026603577303)
                ·
                  refine ⟨11087178357292539905365955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391452238195026603577303 11087178357292539905365955)
                  ·
                    refine ⟨16630767535938809858048933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11087178357292539905365955 16630767535938809858048933)
                    ·
                      refine ⟨3118268912988526848384175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16630767535938809858048933 3118268912988526848384175)
                      ·
                        rfl

theorem cell23_6072807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_6072807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072807 prefixEnd_6072807 := by exact prefixLift 6072807
  have htrace : WordTrace (prefixWord ++ tailWord_6072807) baseStart_6072807 baseEnd_6072807 := by
    simpa [prefixWord, tailWord_6072807, baseEnd_6072807] using wordTrace_append hprefix tailTrace_6072807
  have hstable : (prefixWord ++ tailWord_6072807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072807).length < 2 ^ (prefixWord ++ tailWord_6072807).sum := by decide
  have hdescent : baseEnd_6072807 < baseStart_6072807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072824 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 3, 2, 2]
def baseStart_6072824 : Nat := 118140960795 + 6072824 * 2 ^ 59
def prefixEnd_6072824 : Nat := 4983230072969 + 3 ^ 40 * 6072824 * 2
def baseEnd_6072824 : Nat := 3118277642159653281871597

theorem tailTrace_6072824 : CollatzResearch.WordTrace tailWord_6072824 prefixEnd_6072824 3118277642159653281871597 := by
  unfold tailWord_6072824
  simp only [CollatzResearch.WordTrace]
  refine ⟨110747043875601639306060763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147662725167468852408081017 110747043875601639306060763)
  ·
    refine ⟨166120565813402458959091145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110747043875601639306060763 166120565813402458959091145)
    ·
      refine ⟨124590424360051844219318359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166120565813402458959091145 124590424360051844219318359)
      ·
        refine ⟨186885636540077766328977539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124590424360051844219318359 186885636540077766328977539)
        ·
          refine ⟨280328454810116649493466309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186885636540077766328977539 280328454810116649493466309)
          ·
            refine ⟨52561585276896871780024933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280328454810116649493466309 52561585276896871780024933)
            ·
              refine ⟨9855297239418163458754675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52561585276896871780024933 9855297239418163458754675)
              ·
                refine ⟨14782945859127245188132013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9855297239418163458754675 14782945859127245188132013)
                ·
                  refine ⟨5543604697172716945549505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14782945859127245188132013 5543604697172716945549505)
                  ·
                    refine ⟨4157703522879537709162129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543604697172716945549505 4157703522879537709162129)
                    ·
                      refine ⟨3118277642159653281871597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157703522879537709162129 3118277642159653281871597)
                      ·
                        rfl

theorem cell23_6072824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_6072824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072824 prefixEnd_6072824 := by exact prefixLift 6072824
  have htrace : WordTrace (prefixWord ++ tailWord_6072824) baseStart_6072824 baseEnd_6072824 := by
    simpa [prefixWord, tailWord_6072824, baseEnd_6072824] using wordTrace_append hprefix tailTrace_6072824
  have hstable : (prefixWord ++ tailWord_6072824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072824).length < 2 ^ (prefixWord ++ tailWord_6072824).sum := by decide
  have hdescent : baseEnd_6072824 < baseStart_6072824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072838 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6072838 : Nat := 118140960795 + 6072838 * 2 ^ 59
def prefixEnd_6072838 : Nat := 4983230072969 + 3 ^ 40 * 6072838 * 2
def baseEnd_6072838 : Nat := 1039428276962938742365511

theorem tailTrace_6072838 : CollatzResearch.WordTrace tailWord_6072838 prefixEnd_6072838 1039428276962938742365511 := by
  unfold tailWord_6072838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921706199161017468847849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147663065582101706002087445 6921706199161017468847849)
  ·
    refine ⟨5191279649370763101635887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6921706199161017468847849 5191279649370763101635887)
    ·
      refine ⟨7786919474056144652453831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191279649370763101635887 7786919474056144652453831)
      ·
        refine ⟨11680379211084216978680747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7786919474056144652453831 11680379211084216978680747)
        ·
          refine ⟨17520568816626325468021121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11680379211084216978680747 17520568816626325468021121)
          ·
            refine ⟨13140426612469744101015841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17520568816626325468021121 13140426612469744101015841)
            ·
              refine ⟨9855319959352308075761881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13140426612469744101015841 9855319959352308075761881)
              ·
                refine ⟨7391489969514231056821411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9855319959352308075761881 7391489969514231056821411)
                ·
                  refine ⟨11087234954271346585232117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391489969514231056821411 11087234954271346585232117)
                  ·
                    refine ⟨1039428276962938742365511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11087234954271346585232117 1039428276962938742365511)
                    ·
                      rfl

theorem cell23_6072838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6072838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072838 prefixEnd_6072838 := by exact prefixLift 6072838
  have htrace : WordTrace (prefixWord ++ tailWord_6072838) baseStart_6072838 baseEnd_6072838 := by
    simpa [prefixWord, tailWord_6072838, baseEnd_6072838] using wordTrace_append hprefix tailTrace_6072838
  have hstable : (prefixWord ++ tailWord_6072838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072838).length < 2 ^ (prefixWord ++ tailWord_6072838).sum := by decide
  have hdescent : baseEnd_6072838 < baseStart_6072838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072844 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_6072844 : Nat := 118140960795 + 6072844 * 2 ^ 59
def prefixEnd_6072844 : Nat := 4983230072969 + 3 ^ 40 * 6072844 * 2
def baseEnd_6072844 : Nat := 3118287911772743203621505

theorem tailTrace_6072844 : CollatzResearch.WordTrace tailWord_6072844 prefixEnd_6072844 3118287911772743203621505 := by
  unfold tailWord_6072844
  simp only [CollatzResearch.WordTrace]
  refine ⟨110747408605565411013924793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147663211474087214685233057 110747408605565411013924793)
  ·
    refine ⟨83060556454174058260443595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110747408605565411013924793 83060556454174058260443595)
    ·
      refine ⟨124590834681261087390665393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83060556454174058260443595 124590834681261087390665393)
      ·
        refine ⟨93443126010945815542999045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124590834681261087390665393 93443126010945815542999045)
        ·
          refine ⟨17520586127052340414312321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93443126010945815542999045 17520586127052340414312321)
          ·
            refine ⟨13140439595289255310734241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17520586127052340414312321 13140439595289255310734241)
            ·
              refine ⟨9855329696466941483050681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13140439595289255310734241 9855329696466941483050681)
              ·
                refine ⟨7391497272350206112288011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9855329696466941483050681 7391497272350206112288011)
                ·
                  refine ⟨11087245908525309168432017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391497272350206112288011 11087245908525309168432017)
                  ·
                    refine ⟨8315434431393981876324013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11087245908525309168432017 8315434431393981876324013)
                    ·
                      refine ⟨3118287911772743203621505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8315434431393981876324013 3118287911772743203621505)
                      ·
                        rfl

theorem cell23_6072844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_6072844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072844 prefixEnd_6072844 := by exact prefixLift 6072844
  have htrace : WordTrace (prefixWord ++ tailWord_6072844) baseStart_6072844 baseEnd_6072844 := by
    simpa [prefixWord, tailWord_6072844, baseEnd_6072844] using wordTrace_append hprefix tailTrace_6072844
  have hstable : (prefixWord ++ tailWord_6072844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072844).length < 2 ^ (prefixWord ++ tailWord_6072844).sum := by decide
  have hdescent : baseEnd_6072844 < baseStart_6072844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072874 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_6072874 : Nat := 118140960795 + 6072874 * 2 ^ 59
def prefixEnd_6072874 : Nat := 4983230072969 + 3 ^ 40 * 6072874 * 2
def baseEnd_6072874 : Nat := 3118303316192378086246367

theorem tailTrace_6072874 : CollatzResearch.WordTrace tailWord_6072874 prefixEnd_6072874 3118303316192378086246367 := by
  unfold tailWord_6072874
  simp only [CollatzResearch.WordTrace]
  refine ⟨55373977850255534287860419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147663940934014758100961117 55373977850255534287860419)
  ·
    refine ⟨83060966775383301431790629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55373977850255534287860419 83060966775383301431790629)
    ·
      refine ⟨15573931270384369018460743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83060966775383301431790629 15573931270384369018460743)
      ·
        refine ⟨23360896905576553527691115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15573931270384369018460743 23360896905576553527691115)
        ·
          refine ⟨35041345358364830291536673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23360896905576553527691115 35041345358364830291536673)
          ·
            refine ⟨26281009018773622718652505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35041345358364830291536673 26281009018773622718652505)
            ·
              refine ⟨19710756764080217038989379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26281009018773622718652505 19710756764080217038989379)
              ·
                refine ⟨29566135146120325558484069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19710756764080217038989379 29566135146120325558484069)
                ·
                  refine ⟨5543650339897561042215763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29566135146120325558484069 5543650339897561042215763)
                  ·
                    refine ⟨8315475509846341563323645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5543650339897561042215763 8315475509846341563323645)
                    ·
                      refine ⟨3118303316192378086246367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8315475509846341563323645 3118303316192378086246367)
                      ·
                        rfl

theorem cell23_6072874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_6072874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072874 prefixEnd_6072874 := by exact prefixLift 6072874
  have htrace : WordTrace (prefixWord ++ tailWord_6072874) baseStart_6072874 baseEnd_6072874 := by
    simpa [prefixWord, tailWord_6072874, baseEnd_6072874] using wordTrace_append hprefix tailTrace_6072874
  have hstable : (prefixWord ++ tailWord_6072874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072874).length < 2 ^ (prefixWord ++ tailWord_6072874).sum := by decide
  have hdescent : baseEnd_6072874 < baseStart_6072874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072901 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 1, 3, 2]
def baseStart_6072901 : Nat := 118140960795 + 6072901 * 2 ^ 59
def prefixEnd_6072901 : Nat := 4983230072969 + 3 ^ 40 * 6072901 * 2
def baseEnd_6072901 : Nat := 3118317180170049480608743

theorem tailTrace_6072901 : CollatzResearch.WordTrace tailWord_6072901 prefixEnd_6072901 3118317180170049480608743 := by
  unfold tailWord_6072901
  simp only [CollatzResearch.WordTrace]
  refine ⟨221496896171924320762674557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147664597447949547175116371 221496896171924320762674557)
  ·
    refine ⟨83061336064471620286002959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221496896171924320762674557 83061336064471620286002959)
    ·
      refine ⟨124592004096707430429004439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83061336064471620286002959 124592004096707430429004439)
      ·
        refine ⟨186888006145061145643506659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124592004096707430429004439 186888006145061145643506659)
        ·
          refine ⟨280332009217591718465259989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186888006145061145643506659 280332009217591718465259989)
          ·
            refine ⟨6570281466037305901529531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 280332009217591718465259989 6570281466037305901529531)
            ·
              refine ⟨9855422199055958852294297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570281466037305901529531 9855422199055958852294297)
              ·
                refine ⟨7391566649291969139220723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9855422199055958852294297 7391566649291969139220723)
                ·
                  refine ⟨11087349973937953708831085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391566649291969139220723 11087349973937953708831085)
                  ·
                    refine ⟨4157756240226732640811657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11087349973937953708831085 4157756240226732640811657)
                    ·
                      refine ⟨3118317180170049480608743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157756240226732640811657 3118317180170049480608743)
                      ·
                        rfl

theorem cell23_6072901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_6072901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072901 prefixEnd_6072901 := by exact prefixLift 6072901
  have htrace : WordTrace (prefixWord ++ tailWord_6072901) baseStart_6072901 baseEnd_6072901 := by
    simpa [prefixWord, tailWord_6072901, baseEnd_6072901] using wordTrace_append hprefix tailTrace_6072901
  have hstable : (prefixWord ++ tailWord_6072901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072901).length < 2 ^ (prefixWord ++ tailWord_6072901).sum := by decide
  have hdescent : baseEnd_6072901 < baseStart_6072901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072914 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_6072914 : Nat := 118140960795 + 6072914 * 2 ^ 59
def prefixEnd_6072914 : Nat := 4983230072969 + 3 ^ 40 * 6072914 * 2
def baseEnd_6072914 : Nat := 3118323855418557929746183

theorem tailTrace_6072914 : CollatzResearch.WordTrace tailWord_6072914 prefixEnd_6072914 3118323855418557929746183 := by
  unfold tailWord_6072914
  simp only [CollatzResearch.WordTrace]
  refine ⟨55374342580219305995724449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147664913547251482655265197 55374342580219305995724449)
  ·
    refine ⟨41530756935164479496793337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55374342580219305995724449 41530756935164479496793337)
    ·
      refine ⟨31148067701373359622595003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41530756935164479496793337 31148067701373359622595003)
      ·
        refine ⟨46722101552060039433892505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31148067701373359622595003 46722101552060039433892505)
        ·
          refine ⟨35041576164045029575419379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46722101552060039433892505 35041576164045029575419379)
          ·
            refine ⟨52562364246067544363129069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35041576164045029575419379 52562364246067544363129069)
            ·
              refine ⟨19710886592275329136173401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52562364246067544363129069 19710886592275329136173401)
              ·
                refine ⟨14783164944206496852130051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19710886592275329136173401 14783164944206496852130051)
                ·
                  refine ⟨22174747416309745278195077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14783164944206496852130051 22174747416309745278195077)
                  ·
                    refine ⟨4157765140558077239661577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22174747416309745278195077 4157765140558077239661577)
                    ·
                      refine ⟨3118323855418557929746183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157765140558077239661577 3118323855418557929746183)
                      ·
                        rfl

theorem cell23_6072914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_6072914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072914 prefixEnd_6072914 := by exact prefixLift 6072914
  have htrace : WordTrace (prefixWord ++ tailWord_6072914) baseStart_6072914 baseEnd_6072914 := by
    simpa [prefixWord, tailWord_6072914, baseEnd_6072914] using wordTrace_append hprefix tailTrace_6072914
  have hstable : (prefixWord ++ tailWord_6072914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072914).length < 2 ^ (prefixWord ++ tailWord_6072914).sum := by decide
  have hdescent : baseEnd_6072914 < baseStart_6072914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072926 : List Nat := [4, 4, 1, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6072926 : Nat := 118140960795 + 6072926 * 2 ^ 59
def prefixEnd_6072926 : Nat := 4983230072969 + 3 ^ 40 * 6072926 * 2
def baseEnd_6072926 : Nat := 3118330017186411882796129

theorem tailTrace_6072926 : CollatzResearch.WordTrace tailWord_6072926 prefixEnd_6072926 3118330017186411882796129 := by
  unfold tailWord_6072926
  simp only [CollatzResearch.WordTrace]
  refine ⟨27687225999604218754041829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147665205331222500021556421 27687225999604218754041829)
  ·
    refine ⟨5191354874925791016382843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27687225999604218754041829 5191354874925791016382843)
    ·
      refine ⟨7787032312388686524574265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191354874925791016382843 7787032312388686524574265)
      ·
        refine ⟨5840274234291514893430699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7787032312388686524574265 5840274234291514893430699)
        ·
          refine ⟨8760411351437272340146049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840274234291514893430699 8760411351437272340146049)
          ·
            refine ⟨6570308513577954255109537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8760411351437272340146049 6570308513577954255109537)
            ·
              refine ⟨4927731385183465691332153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6570308513577954255109537 4927731385183465691332153)
              ·
                refine ⟨3695798538887599268499115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4927731385183465691332153 3695798538887599268499115)
                ·
                  refine ⟨5543697808331398902748673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695798538887599268499115 5543697808331398902748673)
                  ·
                    refine ⟨4157773356248549177061505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543697808331398902748673 4157773356248549177061505)
                    ·
                      refine ⟨3118330017186411882796129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157773356248549177061505 3118330017186411882796129)
                      ·
                        rfl

theorem cell23_6072926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6072926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072926 prefixEnd_6072926 := by exact prefixLift 6072926
  have htrace : WordTrace (prefixWord ++ tailWord_6072926) baseStart_6072926 baseEnd_6072926 := by
    simpa [prefixWord, tailWord_6072926, baseEnd_6072926] using wordTrace_append hprefix tailTrace_6072926
  have hstable : (prefixWord ++ tailWord_6072926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072926).length < 2 ^ (prefixWord ++ tailWord_6072926).sum := by decide
  have hdescent : baseEnd_6072926 < baseStart_6072926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6072931 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 2, 2, 2]
def baseStart_6072931 : Nat := 118140960795 + 6072931 * 2 ^ 59
def prefixEnd_6072931 : Nat := 4983230072969 + 3 ^ 40 * 6072931 * 2
def baseEnd_6072931 : Nat := 3118332584589684363233605

theorem tailTrace_6072931 : CollatzResearch.WordTrace tailWord_6072931 prefixEnd_6072931 3118332584589684363233605 := by
  unfold tailWord_6072931
  simp only [CollatzResearch.WordTrace]
  refine ⟨221497990361815635886266647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147665326907877090590844431 221497990361815635886266647)
  ·
    refine ⟨332246985542723453829399971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221497990361815635886266647 332246985542723453829399971)
    ·
      refine ⟨498370478314085180744099957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332246985542723453829399971 498370478314085180744099957)
      ·
        refine ⟨46722232341945485694759371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 498370478314085180744099957 46722232341945485694759371)
        ·
          refine ⟨70083348512918228542139057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46722232341945485694759371 70083348512918228542139057)
          ·
            refine ⟨52562511384688671406604293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70083348512918228542139057 52562511384688671406604293)
            ·
              refine ⟨9855470884629125888738305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52562511384688671406604293 9855470884629125888738305)
              ·
                refine ⟨7391603163471844416553729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9855470884629125888738305 7391603163471844416553729)
                ·
                  refine ⟨5543702372603883312415297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7391603163471844416553729 5543702372603883312415297)
                  ·
                    refine ⟨4157776779452912484311473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543702372603883312415297 4157776779452912484311473)
                    ·
                      refine ⟨3118332584589684363233605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157776779452912484311473 3118332584589684363233605)
                      ·
                        rfl

theorem cell23_6072931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_6072931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6072931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6072931 prefixEnd_6072931 := by exact prefixLift 6072931
  have htrace : WordTrace (prefixWord ++ tailWord_6072931) baseStart_6072931 baseEnd_6072931 := by
    simpa [prefixWord, tailWord_6072931, baseEnd_6072931] using wordTrace_append hprefix tailTrace_6072931
  have hstable : (prefixWord ++ tailWord_6072931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6072931).length < 2 ^ (prefixWord ++ tailWord_6072931).sum := by decide
  have hdescent : baseEnd_6072931 < baseStart_6072931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6072931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073007 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 3]
def baseStart_6073007 : Nat := 118140960795 + 6073007 * 2 ^ 59
def prefixEnd_6073007 : Nat := 4983230072969 + 3 ^ 40 * 6073007 * 2
def baseEnd_6073007 : Nat := 3118371609119426065883255

theorem tailTrace_6073007 : CollatzResearch.WordTrace tailWord_6073007 prefixEnd_6073007 3118371609119426065883255 := by
  unfold tailWord_6073007
  simp only [CollatzResearch.WordTrace]
  refine ⟨221500762309540300866033275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147667174873026867244022183 221500762309540300866033275)
  ·
    refine ⟨332251143464310451299049913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221500762309540300866033275 332251143464310451299049913)
    ·
      refine ⟨249188357598232838474287435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332251143464310451299049913 249188357598232838474287435)
      ·
        refine ⟨373782536397349257711431153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249188357598232838474287435 373782536397349257711431153)
        ·
          refine ⟨280336902298011943283573365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373782536397349257711431153 280336902298011943283573365)
          ·
            refine ⟨26281584590438619682835003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280336902298011943283573365 26281584590438619682835003)
            ·
              refine ⟨39422376885657929524252505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26281584590438619682835003 39422376885657929524252505)
              ·
                refine ⟨29566782664243447143189379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39422376885657929524252505 29566782664243447143189379)
                ·
                  refine ⟨44350173996365170714784069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29566782664243447143189379 44350173996365170714784069)
                  ·
                    refine ⟨8315657624318469509022013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44350173996365170714784069 8315657624318469509022013)
                    ·
                      refine ⟨3118371609119426065883255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8315657624318469509022013 3118371609119426065883255)
                      ·
                        rfl

theorem cell23_6073007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_6073007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073007 prefixEnd_6073007 := by exact prefixLift 6073007
  have htrace : WordTrace (prefixWord ++ tailWord_6073007) baseStart_6073007 baseEnd_6073007 := by
    simpa [prefixWord, tailWord_6073007, baseEnd_6073007] using wordTrace_append hprefix tailTrace_6073007
  have hstable : (prefixWord ++ tailWord_6073007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073007).length < 2 ^ (prefixWord ++ tailWord_6073007).sum := by decide
  have hdescent : baseEnd_6073007 < baseStart_6073007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073040 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 11]
def baseStart_6073040 : Nat := 118140960795 + 6073040 * 2 ^ 59
def prefixEnd_6073040 : Nat := 4983230072969 + 3 ^ 40 * 6073040 * 2
def baseEnd_6073040 : Nat := 1039462851327008145590201

theorem tailTrace_6073040 : CollatzResearch.WordTrace tailWord_6073040 prefixEnd_6073040 1039462851327008145590201 := by
  unfold tailWord_6073040
  simp only [CollatzResearch.WordTrace]
  refine ⟨110750982959210373750992287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147667977278947165001323049 110750982959210373750992287)
  ·
    refine ⟨166126474438815560626488431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110750982959210373750992287 166126474438815560626488431)
    ·
      refine ⟨249189711658223340939732647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166126474438815560626488431 249189711658223340939732647)
      ·
        refine ⟨373784567487335011409598971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249189711658223340939732647 373784567487335011409598971)
        ·
          refine ⟨560676851231002517114398457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373784567487335011409598971 560676851231002517114398457)
          ·
            refine ⟨420507638423251887835798843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560676851231002517114398457 420507638423251887835798843)
            ·
              refine ⟨630761457634877831753698265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420507638423251887835798843 630761457634877831753698265)
              ·
                refine ⟨473071093226158373815273699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630761457634877831753698265 473071093226158373815273699)
                ·
                  refine ⟨709606639839237560722910549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473071093226158373815273699 709606639839237560722910549)
                  ·
                    refine ⟨1039462851327008145590201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 709606639839237560722910549 1039462851327008145590201)
                    ·
                      rfl

theorem cell23_6073040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_6073040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073040 prefixEnd_6073040 := by exact prefixLift 6073040
  have htrace : WordTrace (prefixWord ++ tailWord_6073040) baseStart_6073040 baseEnd_6073040 := by
    simpa [prefixWord, tailWord_6073040, baseEnd_6073040] using wordTrace_append hprefix tailTrace_6073040
  have hstable : (prefixWord ++ tailWord_6073040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073040).length < 2 ^ (prefixWord ++ tailWord_6073040).sum := by decide
  have hdescent : baseEnd_6073040 < baseStart_6073040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073048 : List Nat := [2, 1, 2, 2, 3, 3, 3, 2, 1, 4]
def baseStart_6073048 : Nat := 118140960795 + 6073048 * 2 ^ 59
def prefixEnd_6073048 : Nat := 4983230072969 + 3 ^ 40 * 6073048 * 2
def baseEnd_6073048 : Nat := 1039464220608753468490189

theorem tailTrace_6073048 : CollatzResearch.WordTrace tailWord_6073048 prefixEnd_6073048 1039464220608753468490189 := by
  unfold tailWord_6073048
  simp only [CollatzResearch.WordTrace]
  refine ⟨110751128851195882434137899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147668171801594509912183865 110751128851195882434137899)
  ·
    refine ⟨166126693276793823651206849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110751128851195882434137899 166126693276793823651206849)
    ·
      refine ⟨124595019957595367738405137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166126693276793823651206849 124595019957595367738405137)
      ·
        refine ⟨93446264968196525803803853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124595019957595367738405137 93446264968196525803803853)
        ·
          refine ⟨35042349363073697176426445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93446264968196525803803853 35042349363073697176426445)
          ·
            refine ⟨13140881011152636441159917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35042349363073697176426445 13140881011152636441159917)
            ·
              refine ⟨4927830379182238665434969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13140881011152636441159917 4927830379182238665434969)
              ·
                refine ⟨3695872784386678999076227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4927830379182238665434969 3695872784386678999076227)
                ·
                  refine ⟨5543809176580018498614341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695872784386678999076227 5543809176580018498614341)
                  ·
                    refine ⟨1039464220608753468490189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5543809176580018498614341 1039464220608753468490189)
                    ·
                      rfl

theorem cell23_6073048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_6073048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073048 prefixEnd_6073048 := by exact prefixLift 6073048
  have htrace : WordTrace (prefixWord ++ tailWord_6073048) baseStart_6073048 baseEnd_6073048 := by
    simpa [prefixWord, tailWord_6073048, baseEnd_6073048] using wordTrace_append hprefix tailTrace_6073048
  have hstable : (prefixWord ++ tailWord_6073048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073048).length < 2 ^ (prefixWord ++ tailWord_6073048).sum := by decide
  have hdescent : baseEnd_6073048 < baseStart_6073048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073061 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 6]
def baseStart_6073061 : Nat := 118140960795 + 6073061 * 2 ^ 59
def prefixEnd_6073061 : Nat := 4983230072969 + 3 ^ 40 * 6073061 * 2
def baseEnd_6073061 : Nat := 346488815230529872734223

theorem tailTrace_6073061 : CollatzResearch.WordTrace tailWord_6073061 prefixEnd_6073061 346488815230529872734223 := by
  unfold tailWord_6073061
  simp only [CollatzResearch.WordTrace]
  refine ⟨221502731851344668088499037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147668487900896445392332691 221502731851344668088499037)
  ·
    refine ⟨83063524444254250533187139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221502731851344668088499037 83063524444254250533187139)
    ·
      refine ⟨124595286666381375799780709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83063524444254250533187139 124595286666381375799780709)
      ·
        refine ⟨23361616249946507962458883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124595286666381375799780709 23361616249946507962458883)
        ·
          refine ⟨35042424374919761943688325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23361616249946507962458883 35042424374919761943688325)
          ·
            refine ⟨6570454570297455364441561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35042424374919761943688325 6570454570297455364441561)
            ·
              refine ⟨4927840927723091523331171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6570454570297455364441561 4927840927723091523331171)
              ·
                refine ⟨7391761391584637284996757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927840927723091523331171 7391761391584637284996757)
                ·
                  refine ⟨346488815230529872734223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7391761391584637284996757 346488815230529872734223)
                  ·
                    rfl

theorem cell23_6073061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_6073061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073061 prefixEnd_6073061 := by exact prefixLift 6073061
  have htrace : WordTrace (prefixWord ++ tailWord_6073061) baseStart_6073061 baseEnd_6073061 := by
    simpa [prefixWord, tailWord_6073061, baseEnd_6073061] using wordTrace_append hprefix tailTrace_6073061
  have hstable : (prefixWord ++ tailWord_6073061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073061).length < 2 ^ (prefixWord ++ tailWord_6073061).sum := by decide
  have hdescent : baseEnd_6073061 < baseStart_6073061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073074 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_6073074 : Nat := 118140960795 + 6073074 * 2 ^ 59
def prefixEnd_6073074 : Nat := 4983230072969 + 3 ^ 40 * 6073074 * 2
def baseEnd_6073074 : Nat := 1039468670774425767915149

theorem tailTrace_6073074 : CollatzResearch.WordTrace tailWord_6073074 prefixEnd_6073074 1039468670774425767915149 := by
  unfold tailWord_6073074
  simp only [CollatzResearch.WordTrace]
  refine ⟨55375801500074392827180569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147668804000198380872481517 55375801500074392827180569)
  ·
    refine ⟨41531851125055794620385427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55375801500074392827180569 41531851125055794620385427)
    ·
      refine ⟨62297776687583691930578141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41531851125055794620385427 62297776687583691930578141)
      ·
        refine ⟨23361666257843884473966803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62297776687583691930578141 23361666257843884473966803)
        ·
          refine ⟨35042499386765826710950205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23361666257843884473966803 35042499386765826710950205)
          ·
            refine ⟨13140937270037185016606327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35042499386765826710950205 13140937270037185016606327)
            ·
              refine ⟨19711405905055777524909491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13140937270037185016606327 19711405905055777524909491)
              ·
                refine ⟨29567108857583666287364237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19711405905055777524909491 29567108857583666287364237)
                ·
                  refine ⟨11087665821593874857761589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29567108857583666287364237 11087665821593874857761589)
                  ·
                    refine ⟨1039468670774425767915149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11087665821593874857761589 1039468670774425767915149)
                    ·
                      rfl

theorem cell23_6073074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_6073074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073074 prefixEnd_6073074 := by exact prefixLift 6073074
  have htrace : WordTrace (prefixWord ++ tailWord_6073074) baseStart_6073074 baseEnd_6073074 := by
    simpa [prefixWord, tailWord_6073074, baseEnd_6073074] using wordTrace_append hprefix tailTrace_6073074
  have hstable : (prefixWord ++ tailWord_6073074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073074).length < 2 ^ (prefixWord ++ tailWord_6073074).sum := by decide
  have hdescent : baseEnd_6073074 < baseStart_6073074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073107 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4]
def baseStart_6073107 : Nat := 118140960795 + 6073107 * 2 ^ 59
def prefixEnd_6073107 : Nat := 4983230072969 + 3 ^ 40 * 6073107 * 2
def baseEnd_6073107 : Nat := 3118422957184875674632795

theorem tailTrace_6073107 : CollatzResearch.WordTrace tailWord_6073107 prefixEnd_6073107 3118422957184875674632795 := by
  unfold tailWord_6073107
  simp only [CollatzResearch.WordTrace]
  refine ⟨221504409609178017944673575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147669606406118678629782383 221504409609178017944673575)
  ·
    refine ⟨332256614413767026917010363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221504409609178017944673575 332256614413767026917010363)
    ·
      refine ⟨498384921620650540375515545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332256614413767026917010363 498384921620650540375515545)
      ·
        refine ⟨373788691215487905281636659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498384921620650540375515545 373788691215487905281636659)
        ·
          refine ⟨560683036823231857922454989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373788691215487905281636659 560683036823231857922454989)
          ·
            refine ⟨210256138808711946720920621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 560683036823231857922454989 210256138808711946720920621)
            ·
              refine ⟨78846052053266980020345233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210256138808711946720920621 78846052053266980020345233)
              ·
                refine ⟨59134539039950235015258925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78846052053266980020345233 59134539039950235015258925)
                ·
                  refine ⟨22175452139981338130722097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59134539039950235015258925 22175452139981338130722097)
                  ·
                    refine ⟨16631589104986003598041573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22175452139981338130722097 16631589104986003598041573)
                    ·
                      refine ⟨3118422957184875674632795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16631589104986003598041573 3118422957184875674632795)
                      ·
                        rfl

theorem cell23_6073107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_6073107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073107 prefixEnd_6073107 := by exact prefixLift 6073107
  have htrace : WordTrace (prefixWord ++ tailWord_6073107) baseStart_6073107 baseEnd_6073107 := by
    simpa [prefixWord, tailWord_6073107, baseEnd_6073107] using wordTrace_append hprefix tailTrace_6073107
  have hstable : (prefixWord ++ tailWord_6073107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073107).length < 2 ^ (prefixWord ++ tailWord_6073107).sum := by decide
  have hdescent : baseEnd_6073107 < baseStart_6073107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073114 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_6073114 : Nat := 118140960795 + 6073114 * 2 ^ 59
def prefixEnd_6073114 : Nat := 4983230072969 + 3 ^ 40 * 6073114 * 2
def baseEnd_6073114 : Nat := 3118426551549457147245263

theorem tailTrace_6073114 : CollatzResearch.WordTrace tailWord_6073114 prefixEnd_6073114 3118426551549457147245263 := by
  unfold tailWord_6073114
  simp only [CollatzResearch.WordTrace]
  refine ⟨55376166230038164535044599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147669776613435105426785597 55376166230038164535044599)
  ·
    refine ⟨83064249345057246802566899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55376166230038164535044599 83064249345057246802566899)
    ·
      refine ⟨124596374017585870203850349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83064249345057246802566899 124596374017585870203850349)
      ·
        refine ⟨46723640256594701326443881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124596374017585870203850349 46723640256594701326443881)
        ·
          refine ⟨35042730192446025994832911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46723640256594701326443881 35042730192446025994832911)
          ·
            refine ⟨52564095288669038992249367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35042730192446025994832911 52564095288669038992249367)
            ·
              refine ⟨78846142933003558488374051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52564095288669038992249367 78846142933003558488374051)
              ·
                refine ⟨118269214399505337732561077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78846142933003558488374051 118269214399505337732561077)
                ·
                  refine ⟨11087738849953625412427601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118269214399505337732561077 11087738849953625412427601)
                  ·
                    refine ⟨8315804137465219059320701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11087738849953625412427601 8315804137465219059320701)
                    ·
                      refine ⟨3118426551549457147245263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8315804137465219059320701 3118426551549457147245263)
                      ·
                        rfl

theorem cell23_6073114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_6073114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073114 prefixEnd_6073114 := by exact prefixLift 6073114
  have htrace : WordTrace (prefixWord ++ tailWord_6073114) baseStart_6073114 baseEnd_6073114 := by
    simpa [prefixWord, tailWord_6073114, baseEnd_6073114] using wordTrace_append hprefix tailTrace_6073114
  have hstable : (prefixWord ++ tailWord_6073114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073114).length < 2 ^ (prefixWord ++ tailWord_6073114).sum := by decide
  have hdescent : baseEnd_6073114 < baseStart_6073114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073128 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_6073128 : Nat := 118140960795 + 6073128 * 2 ^ 59
def prefixEnd_6073128 : Nat := 4983230072969 + 3 ^ 40 * 6073128 * 2
def baseEnd_6073128 : Nat := 3118433740278620092470199

theorem tailTrace_6073128 : CollatzResearch.WordTrace tailWord_6073128 prefixEnd_6073128 3118433740278620092470199 := by
  unfold tailWord_6073128
  simp only [CollatzResearch.WordTrace]
  refine ⟨110752587771050969265594019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147670117028067959020792025 110752587771050969265594019)
  ·
    refine ⟨166128881656576453898391029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110752587771050969265594019 166128881656576453898391029)
    ·
      refine ⟨15574582655304042552974159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166128881656576453898391029 15574582655304042552974159)
      ·
        refine ⟨23361873982956063829461239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15574582655304042552974159 23361873982956063829461239)
        ·
          refine ⟨35042810974434095744191859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23361873982956063829461239 35042810974434095744191859)
          ·
            refine ⟨52564216461651143616287789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35042810974434095744191859 52564216461651143616287789)
            ·
              refine ⟨19711581173119178856107921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52564216461651143616287789 19711581173119178856107921)
              ·
                refine ⟨14783685879839384142080941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19711581173119178856107921 14783685879839384142080941)
                ·
                  refine ⟨5543882204939769053280353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14783685879839384142080941 5543882204939769053280353)
                  ·
                    refine ⟨4157911653704826789960265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5543882204939769053280353 4157911653704826789960265)
                    ·
                      refine ⟨3118433740278620092470199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157911653704826789960265 3118433740278620092470199)
                      ·
                        rfl

theorem cell23_6073128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_6073128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073128 prefixEnd_6073128 := by exact prefixLift 6073128
  have htrace : WordTrace (prefixWord ++ tailWord_6073128) baseStart_6073128 baseEnd_6073128 := by
    simpa [prefixWord, tailWord_6073128, baseEnd_6073128] using wordTrace_append hprefix tailTrace_6073128
  have hstable : (prefixWord ++ tailWord_6073128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073128).length < 2 ^ (prefixWord ++ tailWord_6073128).sum := by decide
  have hdescent : baseEnd_6073128 < baseStart_6073128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073142 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_6073142 : Nat := 118140960795 + 6073142 * 2 ^ 59
def prefixEnd_6073142 : Nat := 4983230072969 + 3 ^ 40 * 6073142 * 2
def baseEnd_6073142 : Nat := 1039480309669261012565045

theorem tailTrace_6073142 : CollatzResearch.WordTrace tailWord_6073142 prefixEnd_6073142 1039480309669261012565045 := by
  unfold tailWord_6073142
  simp only [CollatzResearch.WordTrace]
  refine ⟨13844105385253201182637355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 147670457442700812614798453 13844105385253201182637355)
  ·
    refine ⟨20766158077879801773956033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13844105385253201182637355 20766158077879801773956033)
    ·
      refine ⟨15574618558409851330467025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20766158077879801773956033 15574618558409851330467025)
      ·
        refine ⟨11680963918807388497850269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15574618558409851330467025 11680963918807388497850269)
        ·
          refine ⟨4380361469552770686693851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11680963918807388497850269 4380361469552770686693851)
          ·
            refine ⟨6570542204329156030040777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380361469552770686693851 6570542204329156030040777)
            ·
              refine ⟨4927906653246867022530583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6570542204329156030040777 4927906653246867022530583)
              ·
                refine ⟨7391859979870300533795875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4927906653246867022530583 7391859979870300533795875)
                ·
                  refine ⟨11087789969805450800693813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391859979870300533795875 11087789969805450800693813)
                  ·
                    refine ⟨1039480309669261012565045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11087789969805450800693813 1039480309669261012565045)
                    ·
                      rfl

theorem cell23_6073142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_6073142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073142 prefixEnd_6073142 := by exact prefixLift 6073142
  have htrace : WordTrace (prefixWord ++ tailWord_6073142) baseStart_6073142 baseEnd_6073142 := by
    simpa [prefixWord, tailWord_6073142, baseEnd_6073142] using wordTrace_append hprefix tailTrace_6073142
  have hstable : (prefixWord ++ tailWord_6073142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073142).length < 2 ^ (prefixWord ++ tailWord_6073142).sum := by decide
  have hdescent : baseEnd_6073142 < baseStart_6073142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073144 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_6073144 : Nat := 118140960795 + 6073144 * 2 ^ 59
def prefixEnd_6073144 : Nat := 4983230072969 + 3 ^ 40 * 6073144 * 2
def baseEnd_6073144 : Nat := 3118441955969092029870125

theorem tailTrace_6073144 : CollatzResearch.WordTrace tailWord_6073144 prefixEnd_6073144 3118441955969092029870125 := by
  unfold tailWord_6073144
  simp only [CollatzResearch.WordTrace]
  refine ⟨110752879555021986631885243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147670506073362648842513657 110752879555021986631885243)
  ·
    refine ⟨166129319332532979947827865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110752879555021986631885243 166129319332532979947827865)
    ·
      refine ⟨124596989499399734960870899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166129319332532979947827865 124596989499399734960870899)
      ·
        refine ⟨186895484249099602441306349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124596989499399734960870899 186895484249099602441306349)
        ·
          refine ⟨70085806593412350915489881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186895484249099602441306349 70085806593412350915489881)
          ·
            refine ⟨52564354945059263186617411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70085806593412350915489881 52564354945059263186617411)
            ·
              refine ⟨78846532417588894779926117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52564354945059263186617411 78846532417588894779926117)
              ·
                refine ⟨14783724828297917771236147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78846532417588894779926117 14783724828297917771236147)
                ·
                  refine ⟨22175587242446876656854221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14783724828297917771236147 22175587242446876656854221)
                  ·
                    refine ⟨8315845215917578746320333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22175587242446876656854221 8315845215917578746320333)
                    ·
                      refine ⟨3118441955969092029870125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8315845215917578746320333 3118441955969092029870125)
                      ·
                        rfl

theorem cell23_6073144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_6073144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073144 prefixEnd_6073144 := by exact prefixLift 6073144
  have htrace : WordTrace (prefixWord ++ tailWord_6073144) baseStart_6073144 baseEnd_6073144 := by
    simpa [prefixWord, tailWord_6073144, baseEnd_6073144] using wordTrace_append hprefix tailTrace_6073144
  have hstable : (prefixWord ++ tailWord_6073144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073144).length < 2 ^ (prefixWord ++ tailWord_6073144).sum := by decide
  have hdescent : baseEnd_6073144 < baseStart_6073144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073157 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_6073157 : Nat := 118140960795 + 6073157 * 2 ^ 59
def prefixEnd_6073157 : Nat := 4983230072969 + 3 ^ 40 * 6073157 * 2
def baseEnd_6073157 : Nat := 3118448631217600479007565

theorem tailTrace_6073157 : CollatzResearch.WordTrace tailWord_6073157 prefixEnd_6073157 3118448631217600479007565 := by
  unfold tailWord_6073157
  simp only [CollatzResearch.WordTrace]
  refine ⟨221506233258996876483993725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147670822172664584322662483 221506233258996876483993725)
  ·
    refine ⟨83064837472123828681497647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221506233258996876483993725 83064837472123828681497647)
    ·
      refine ⟨124597256208185743022246471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83064837472123828681497647 124597256208185743022246471)
      ·
        refine ⟨186895884312278614533369707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124597256208185743022246471 186895884312278614533369707)
        ·
          refine ⟨280343826468417921800054561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186895884312278614533369707 280343826468417921800054561)
          ·
            refine ⟨210257869851313441350040921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280343826468417921800054561 210257869851313441350040921)
            ·
              refine ⟨157693402388485081012530691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210257869851313441350040921 157693402388485081012530691)
              ·
                refine ⟨236540103582727621518796037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157693402388485081012530691 236540103582727621518796037)
                ·
                  refine ⟨44351269421761429034774257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 236540103582727621518796037 44351269421761429034774257)
                  ·
                    refine ⟨33263452066321071776080693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44351269421761429034774257 33263452066321071776080693)
                    ·
                      refine ⟨3118448631217600479007565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33263452066321071776080693 3118448631217600479007565)
                      ·
                        rfl

theorem cell23_6073157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_6073157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073157 prefixEnd_6073157 := by exact prefixLift 6073157
  have htrace : WordTrace (prefixWord ++ tailWord_6073157) baseStart_6073157 baseEnd_6073157 := by
    simpa [prefixWord, tailWord_6073157, baseEnd_6073157] using wordTrace_append hprefix tailTrace_6073157
  have hstable : (prefixWord ++ tailWord_6073157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073157).length < 2 ^ (prefixWord ++ tailWord_6073157).sum := by decide
  have hdescent : baseEnd_6073157 < baseStart_6073157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073161 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 3]
def baseStart_6073161 : Nat := 118140960795 + 6073161 * 2 ^ 59
def prefixEnd_6073161 : Nat := 4983230072969 + 3 ^ 40 * 6073161 * 2
def baseEnd_6073161 : Nat := 3118450685140218463357547

theorem tailTrace_6073161 : CollatzResearch.WordTrace tailWord_6073161 prefixEnd_6073161 3118450685140218463357547 := by
  unfold tailWord_6073161
  simp only [CollatzResearch.WordTrace]
  refine ⟨221506379150982385167139337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147670919433988256778092891 221506379150982385167139337)
  ·
    refine ⟨166129784363236788875354503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221506379150982385167139337 166129784363236788875354503)
    ·
      refine ⟨249194676544855183313031755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166129784363236788875354503 249194676544855183313031755)
      ·
        refine ⟨373792014817282774969547633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249194676544855183313031755 373792014817282774969547633)
        ·
          refine ⟨280344011112962081227160725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373792014817282774969547633 280344011112962081227160725)
          ·
            refine ⟨13141125520920097557523159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 280344011112962081227160725 13141125520920097557523159)
            ·
              refine ⟨19711688281380146336284739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13141125520920097557523159 19711688281380146336284739)
              ·
                refine ⟨29567532422070219504427109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19711688281380146336284739 29567532422070219504427109)
                ·
                  refine ⟨5543912329138166157080083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29567532422070219504427109 5543912329138166157080083)
                  ·
                    refine ⟨8315868493707249235620125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5543912329138166157080083 8315868493707249235620125)
                    ·
                      refine ⟨3118450685140218463357547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8315868493707249235620125 3118450685140218463357547)
                      ·
                        rfl

theorem cell23_6073161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 1, 3].length) (baseStart_6073161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073161 prefixEnd_6073161 := by exact prefixLift 6073161
  have htrace : WordTrace (prefixWord ++ tailWord_6073161) baseStart_6073161 baseEnd_6073161 := by
    simpa [prefixWord, tailWord_6073161, baseEnd_6073161] using wordTrace_append hprefix tailTrace_6073161
  have hstable : (prefixWord ++ tailWord_6073161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073161).length < 2 ^ (prefixWord ++ tailWord_6073161).sum := by decide
  have hdescent : baseEnd_6073161 < baseStart_6073161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073188 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_6073188 : Nat := 118140960795 + 6073188 * 2 ^ 59
def prefixEnd_6073188 : Nat := 4983230072969 + 3 ^ 40 * 6073188 * 2
def baseEnd_6073188 : Nat := 3118464549117889857719923

theorem tailTrace_6073188 : CollatzResearch.WordTrace tailWord_6073188 prefixEnd_6073188 3118464549117889857719923 := by
  unfold tailWord_6073188
  simp only [CollatzResearch.WordTrace]
  refine ⟨110753681960942284389186109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147671575947923045852248145 110753681960942284389186109)
  ·
    refine ⟨41532630735353356645944791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110753681960942284389186109 41532630735353356645944791)
    ·
      refine ⟨62298946103030034968917187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41532630735353356645944791 62298946103030034968917187)
      ·
        refine ⟨93448419154545052453375781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62298946103030034968917187 93448419154545052453375781)
        ·
          refine ⟨17521578591477197335007959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93448419154545052453375781 17521578591477197335007959)
          ·
            refine ⟨26282367887215796002511939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17521578591477197335007959 26282367887215796002511939)
            ·
              refine ⟨39423551830823694003767909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26282367887215796002511939 39423551830823694003767909)
              ·
                refine ⟨7391915968279442625706483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39423551830823694003767909 7391915968279442625706483)
                ·
                  refine ⟨11087873952419163938559725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7391915968279442625706483 11087873952419163938559725)
                  ·
                    refine ⟨4157952732157186476959897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11087873952419163938559725 4157952732157186476959897)
                    ·
                      refine ⟨3118464549117889857719923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4157952732157186476959897 3118464549117889857719923)
                      ·
                        rfl

theorem cell23_6073188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_6073188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073188 prefixEnd_6073188 := by exact prefixLift 6073188
  have htrace : WordTrace (prefixWord ++ tailWord_6073188) baseStart_6073188 baseEnd_6073188 := by
    simpa [prefixWord, tailWord_6073188, baseEnd_6073188] using wordTrace_append hprefix tailTrace_6073188
  have hstable : (prefixWord ++ tailWord_6073188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073188).length < 2 ^ (prefixWord ++ tailWord_6073188).sum := by decide
  have hdescent : baseEnd_6073188 < baseStart_6073188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073207 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 9]
def baseStart_6073207 : Nat := 118140960795 + 6073207 * 2 ^ 59
def prefixEnd_6073207 : Nat := 4983230072969 + 3 ^ 40 * 6073207 * 2
def baseEnd_6073207 : Nat := 346497145027813920375815

theorem tailTrace_6073207 : CollatzResearch.WordTrace tailWord_6073207 prefixEnd_6073207 346497145027813920375815 := by
  unfold tailWord_6073207
  simp only [CollatzResearch.WordTrace]
  refine ⟨221508056908815735023313875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147672037939210490015542583 221508056908815735023313875)
  ·
    refine ⟨332262085363223602534970813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221508056908815735023313875 332262085363223602534970813)
    ·
      refine ⟨124598282011208850950614055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332262085363223602534970813 124598282011208850950614055)
      ·
        refine ⟨186897423016813276425921083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124598282011208850950614055 186897423016813276425921083)
        ·
          refine ⟨280346134525219914638881625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186897423016813276425921083 280346134525219914638881625)
          ·
            refine ⟨210259600893914935979161219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280346134525219914638881625 210259600893914935979161219)
            ·
              refine ⟨315389401340872403968741829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210259600893914935979161219 315389401340872403968741829)
              ·
                refine ⟨59135512751413575744139093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 315389401340872403968741829 59135512751413575744139093)
                ·
                  refine ⟨346497145027813920375815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59135512751413575744139093 346497145027813920375815)
                  ·
                    rfl

theorem cell23_6073207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 9].length) (baseStart_6073207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073207 prefixEnd_6073207 := by exact prefixLift 6073207
  have htrace : WordTrace (prefixWord ++ tailWord_6073207) baseStart_6073207 baseEnd_6073207 := by
    simpa [prefixWord, tailWord_6073207, baseEnd_6073207] using wordTrace_append hprefix tailTrace_6073207
  have hstable : (prefixWord ++ tailWord_6073207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073207).length < 2 ^ (prefixWord ++ tailWord_6073207).sum := by decide
  have hdescent : baseEnd_6073207 < baseStart_6073207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073286 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6073286 : Nat := 118140960795 + 6073286 * 2 ^ 59
def prefixEnd_6073286 : Nat := 4983230072969 + 3 ^ 40 * 6073286 * 2
def baseEnd_6073286 : Nat := 3118514870222030474294473

theorem tailTrace_6073286 : CollatzResearch.WordTrace tailWord_6073286 prefixEnd_6073286 3118514870222030474294473 := by
  unfold tailWord_6073286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6922216821110297859857491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147673958850353021010293141 6922216821110297859857491)
  ·
    refine ⟨10383325231665446789786237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6922216821110297859857491 10383325231665446789786237)
    ·
      refine ⟨3893746961874542546169839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10383325231665446789786237 3893746961874542546169839)
      ·
        refine ⟨5840620442811813819254759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893746961874542546169839 5840620442811813819254759)
        ·
          refine ⟨8760930664217720728882139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840620442811813819254759 8760930664217720728882139)
          ·
            refine ⟨13141395996326581093323209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8760930664217720728882139 13141395996326581093323209)
            ·
              refine ⟨9856046997244935819992407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13141395996326581093323209 9856046997244935819992407)
              ·
                refine ⟨14784070495867403729988611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9856046997244935819992407 14784070495867403729988611)
                ·
                  refine ⟨22176105743801105594982917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14784070495867403729988611 22176105743801105594982917)
                  ·
                    refine ⟨4158019826962707299059297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22176105743801105594982917 4158019826962707299059297)
                    ·
                      refine ⟨3118514870222030474294473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158019826962707299059297 3118514870222030474294473)
                      ·
                        rfl

theorem cell23_6073286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6073286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073286 prefixEnd_6073286 := by exact prefixLift 6073286
  have htrace : WordTrace (prefixWord ++ tailWord_6073286) baseStart_6073286 baseEnd_6073286 := by
    simpa [prefixWord, tailWord_6073286, baseEnd_6073286] using wordTrace_append hprefix tailTrace_6073286
  have hstable : (prefixWord ++ tailWord_6073286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073286).length < 2 ^ (prefixWord ++ tailWord_6073286).sum := by decide
  have hdescent : baseEnd_6073286 < baseStart_6073286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073291 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 1, 6, 2]
def baseStart_6073291 : Nat := 118140960795 + 6073291 * 2 ^ 59
def prefixEnd_6073291 : Nat := 4983230072969 + 3 ^ 40 * 6073291 * 2
def baseEnd_6073291 : Nat := 3118517437625302954731949

theorem tailTrace_6073291 : CollatzResearch.WordTrace tailWord_6073291 prefixEnd_6073291 3118517437625302954731949 := by
  unfold tailWord_6073291
  simp only [CollatzResearch.WordTrace]
  refine ⟨221511120640511417369371727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147674080427007611579581151 221511120640511417369371727)
  ·
    refine ⟨332266680960767126054057591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221511120640511417369371727 332266680960767126054057591)
    ·
      refine ⟨498400021441150689081086387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332266680960767126054057591 498400021441150689081086387)
      ·
        refine ⟨747600032161726033621629581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498400021441150689081086387 747600032161726033621629581)
        ·
          refine ⟨280350012060647262608111093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747600032161726033621629581 280350012060647262608111093)
          ·
            refine ⟨26282813630685680869510415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280350012060647262608111093 26282813630685680869510415)
            ·
              refine ⟨39424220446028521304265623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26282813630685680869510415 39424220446028521304265623)
              ·
                refine ⟨59136330669042781956398435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39424220446028521304265623 59136330669042781956398435)
                ·
                  refine ⟨88704496003564172934597653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59136330669042781956398435 88704496003564172934597653)
                  ·
                    refine ⟨4158023250167070606309265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88704496003564172934597653 4158023250167070606309265)
                    ·
                      refine ⟨3118517437625302954731949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158023250167070606309265 3118517437625302954731949)
                      ·
                        rfl

theorem cell23_6073291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 6, 2].length) (baseStart_6073291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073291 prefixEnd_6073291 := by exact prefixLift 6073291
  have htrace : WordTrace (prefixWord ++ tailWord_6073291) baseStart_6073291 baseEnd_6073291 := by
    simpa [prefixWord, tailWord_6073291, baseEnd_6073291] using wordTrace_append hprefix tailTrace_6073291
  have hstable : (prefixWord ++ tailWord_6073291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073291).length < 2 ^ (prefixWord ++ tailWord_6073291).sum := by decide
  have hdescent : baseEnd_6073291 < baseStart_6073291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073368 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 1, 5, 2]
def baseStart_6073368 : Nat := 118140960795 + 6073368 * 2 ^ 59
def prefixEnd_6073368 : Nat := 4983230072969 + 3 ^ 40 * 6073368 * 2
def baseEnd_6073368 : Nat := 3118556975635699153469095

theorem tailTrace_6073368 : CollatzResearch.WordTrace tailWord_6073368 prefixEnd_6073368 3118556975635699153469095 := by
  unfold tailWord_6073368
  simp only [CollatzResearch.WordTrace]
  refine ⟨110756964530616229759962379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147675952707488306346616505 110756964530616229759962379)
  ·
    refine ⟨166135446795924344639943569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110756964530616229759962379 166135446795924344639943569)
    ·
      refine ⟨124601585096943258479957677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166135446795924344639943569 124601585096943258479957677)
      ·
        refine ⟨46725594411353721929984129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124601585096943258479957677 46725594411353721929984129)
        ·
          refine ⟨35044195808515291447488097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46725594411353721929984129 35044195808515291447488097)
          ·
            refine ⟨26283146856386468585616073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35044195808515291447488097 26283146856386468585616073)
            ·
              refine ⟨19712360142289851439212055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26283146856386468585616073 19712360142289851439212055)
              ·
                refine ⟨29568540213434777158818083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19712360142289851439212055 29568540213434777158818083)
                ·
                  refine ⟨44352810320152165738227125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29568540213434777158818083 44352810320152165738227125)
                  ·
                    refine ⟨4158075967514265537958793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44352810320152165738227125 4158075967514265537958793)
                    ·
                      refine ⟨3118556975635699153469095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158075967514265537958793 3118556975635699153469095)
                      ·
                        rfl

theorem cell23_6073368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_6073368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073368 prefixEnd_6073368 := by exact prefixLift 6073368
  have htrace : WordTrace (prefixWord ++ tailWord_6073368) baseStart_6073368 baseEnd_6073368 := by
    simpa [prefixWord, tailWord_6073368, baseEnd_6073368] using wordTrace_append hprefix tailTrace_6073368
  have hstable : (prefixWord ++ tailWord_6073368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073368).length < 2 ^ (prefixWord ++ tailWord_6073368).sum := by decide
  have hdescent : baseEnd_6073368 < baseStart_6073368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073378 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_6073378 : Nat := 118140960795 + 6073378 * 2 ^ 59
def prefixEnd_6073378 : Nat := 4983230072969 + 3 ^ 40 * 6073378 * 2
def baseEnd_6073378 : Nat := 1039520703480748038114683

theorem tailTrace_6073378 : CollatzResearch.WordTrace tailWord_6073378 prefixEnd_6073378 1039520703480748038114683 := by
  unfold tailWord_6073378
  simp only [CollatzResearch.WordTrace]
  refine ⟨55378573447799057806947197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147676195860797487485192525 55378573447799057806947197)
  ·
    refine ⟨20766965042924646677605199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55378573447799057806947197 20766965042924646677605199)
    ·
      refine ⟨31150447564386970016407799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20766965042924646677605199 31150447564386970016407799)
      ·
        refine ⟨46725671346580455024611699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31150447564386970016407799 46725671346580455024611699)
        ·
          refine ⟨70088507019870682536917549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46725671346580455024611699 70088507019870682536917549)
          ·
            refine ⟨26283190132451505951344081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70088507019870682536917549 26283190132451505951344081)
            ·
              refine ⟨19712392599338629463508061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26283190132451505951344081 19712392599338629463508061)
              ·
                refine ⟨7392147224751986048815523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19712392599338629463508061 7392147224751986048815523)
                ·
                  refine ⟨11088220837127979073223285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7392147224751986048815523 11088220837127979073223285)
                  ·
                    refine ⟨1039520703480748038114683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11088220837127979073223285 1039520703480748038114683)
                    ·
                      rfl

theorem cell23_6073378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_6073378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073378 prefixEnd_6073378 := by exact prefixLift 6073378
  have htrace : WordTrace (prefixWord ++ tailWord_6073378) baseStart_6073378 baseEnd_6073378 := by
    simpa [prefixWord, tailWord_6073378, baseEnd_6073378] using wordTrace_append hprefix tailTrace_6073378
  have hstable : (prefixWord ++ tailWord_6073378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073378).length < 2 ^ (prefixWord ++ tailWord_6073378).sum := by decide
  have hdescent : baseEnd_6073378 < baseStart_6073378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073392 : List Nat := [2, 1, 1, 1, 2, 4, 5, 2, 1, 1, 3]
def baseStart_6073392 : Nat := 118140960795 + 6073392 * 2 ^ 59
def prefixEnd_6073392 : Nat := 4983230072969 + 3 ^ 40 * 6073392 * 2
def baseEnd_6073392 : Nat := 3118569299171407059568985

theorem tailTrace_6073392 : CollatzResearch.WordTrace tailWord_6073392 prefixEnd_6073392 3118569299171407059568985 := by
  unfold tailWord_6073392
  simp only [CollatzResearch.WordTrace]
  refine ⟨110757402206572755809399215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147676536275430341079198953 110757402206572755809399215)
  ·
    refine ⟨166136103309859133714098823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110757402206572755809399215 166136103309859133714098823)
    ·
      refine ⟨249204154964788700571148235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166136103309859133714098823 249204154964788700571148235)
      ·
        refine ⟨373806232447183050856722353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249204154964788700571148235 373806232447183050856722353)
        ·
          refine ⟨280354674335387288142541765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373806232447183050856722353 280354674335387288142541765)
          ·
            refine ⟨52566501437885116526726581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 280354674335387288142541765 52566501437885116526726581)
            ·
              refine ⟨4928109509801729674380617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52566501437885116526726581 4928109509801729674380617)
              ·
                refine ⟨3696082132351297255785463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928109509801729674380617 3696082132351297255785463)
                ·
                  refine ⟨5544123198526945883678195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696082132351297255785463 5544123198526945883678195)
                  ·
                    refine ⟨8316184797790418825517293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5544123198526945883678195 8316184797790418825517293)
                    ·
                      refine ⟨3118569299171407059568985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8316184797790418825517293 3118569299171407059568985)
                      ·
                        rfl

theorem cell23_6073392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 1, 1, 3].length) (baseStart_6073392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073392 prefixEnd_6073392 := by exact prefixLift 6073392
  have htrace : WordTrace (prefixWord ++ tailWord_6073392) baseStart_6073392 baseEnd_6073392 := by
    simpa [prefixWord, tailWord_6073392, baseEnd_6073392] using wordTrace_append hprefix tailTrace_6073392
  have hstable : (prefixWord ++ tailWord_6073392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073392).length < 2 ^ (prefixWord ++ tailWord_6073392).sum := by decide
  have hdescent : baseEnd_6073392 < baseStart_6073392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073408 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 2, 4]
def baseStart_6073408 : Nat := 118140960795 + 6073408 * 2 ^ 59
def prefixEnd_6073408 : Nat := 4983230072969 + 3 ^ 40 * 6073408 * 2
def baseEnd_6073408 : Nat := 1039525838287292998989637

theorem tailTrace_6073408 : CollatzResearch.WordTrace tailWord_6073408 prefixEnd_6073408 1039525838287292998989637 := by
  unfold tailWord_6073408
  simp only [CollatzResearch.WordTrace]
  refine ⟨110757693990543773175690439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147676925320725030900920585 110757693990543773175690439)
  ·
    refine ⟨166136540985815659763535659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110757693990543773175690439 166136540985815659763535659)
    ·
      refine ⟨249204811478723489645303489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166136540985815659763535659 249204811478723489645303489)
      ·
        refine ⟨186903608609042617233977617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249204811478723489645303489 186903608609042617233977617)
        ·
          refine ⟨140177706456781962925483213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186903608609042617233977617 140177706456781962925483213)
          ·
            refine ⟨52566639921293236097056205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140177706456781962925483213 52566639921293236097056205)
            ·
              refine ⟨19712489970484963536396077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52566639921293236097056205 19712489970484963536396077)
              ·
                refine ⟨7392183738931861326148529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19712489970484963536396077 7392183738931861326148529)
                ·
                  refine ⟨5544137804198895994611397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7392183738931861326148529 5544137804198895994611397)
                  ·
                    refine ⟨1039525838287292998989637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544137804198895994611397 1039525838287292998989637)
                    ·
                      rfl

theorem cell23_6073408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2, 4].length) (baseStart_6073408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073408 prefixEnd_6073408 := by exact prefixLift 6073408
  have htrace : WordTrace (prefixWord ++ tailWord_6073408) baseStart_6073408 baseEnd_6073408 := by
    simpa [prefixWord, tailWord_6073408, baseEnd_6073408] using wordTrace_append hprefix tailTrace_6073408
  have hstable : (prefixWord ++ tailWord_6073408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073408).length < 2 ^ (prefixWord ++ tailWord_6073408).sum := by decide
  have hdescent : baseEnd_6073408 < baseStart_6073408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073411 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4]
def baseStart_6073411 : Nat := 118140960795 + 6073411 * 2 ^ 59
def prefixEnd_6073411 : Nat := 4983230072969 + 3 ^ 40 * 6073411 * 2
def baseEnd_6073411 : Nat := 3118579055303842485231397

theorem tailTrace_6073411 : CollatzResearch.WordTrace tailWord_6073411 prefixEnd_6073411 3118579055303842485231397 := by
  unfold tailWord_6073411
  simp only [CollatzResearch.WordTrace]
  refine ⟨221515497400076677863740087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147676998266717785242493391 221515497400076677863740087)
  ·
    refine ⟨332273246100115016795610131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221515497400076677863740087 332273246100115016795610131)
    ·
      refine ⟨498409869150172525193415197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332273246100115016795610131 498409869150172525193415197)
      ·
        refine ⟨186903700931314696947530699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498409869150172525193415197 186903700931314696947530699)
        ·
          refine ⟨280355551396972045421296049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186903700931314696947530699 280355551396972045421296049)
          ·
            refine ⟨210266663547729034065972037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280355551396972045421296049 210266663547729034065972037)
            ·
              refine ⟨39424999415199193887369757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210266663547729034065972037 39424999415199193887369757)
              ·
                refine ⟨14784374780699697707763659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39424999415199193887369757 14784374780699697707763659)
                ·
                  refine ⟨22176562171049546561645489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14784374780699697707763659 22176562171049546561645489)
                  ·
                    refine ⟨16632421628287159921234117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22176562171049546561645489 16632421628287159921234117)
                    ·
                      refine ⟨3118579055303842485231397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16632421628287159921234117 3118579055303842485231397)
                      ·
                        rfl

theorem cell23_6073411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_6073411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073411 prefixEnd_6073411 := by exact prefixLift 6073411
  have htrace : WordTrace (prefixWord ++ tailWord_6073411) baseStart_6073411 baseEnd_6073411 := by
    simpa [prefixWord, tailWord_6073411, baseEnd_6073411] using wordTrace_append hprefix tailTrace_6073411
  have hstable : (prefixWord ++ tailWord_6073411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073411).length < 2 ^ (prefixWord ++ tailWord_6073411).sum := by decide
  have hdescent : baseEnd_6073411 < baseStart_6073411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073415 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_6073415 : Nat := 118140960795 + 6073415 * 2 ^ 59
def prefixEnd_6073415 : Nat := 4983230072969 + 3 ^ 40 * 6073415 * 2
def baseEnd_6073415 : Nat := 3118581109226460469581379

theorem tailTrace_6073415 : CollatzResearch.WordTrace tailWord_6073415 prefixEnd_6073415 3118581109226460469581379 := by
  unfold tailWord_6073415
  simp only [CollatzResearch.WordTrace]
  refine ⟨221515643292062186546885699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147677095528041457697923799 221515643292062186546885699)
  ·
    refine ⟨332273464938093279820328549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221515643292062186546885699 332273464938093279820328549)
    ·
      refine ⟨62301274675892489966311603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332273464938093279820328549 62301274675892489966311603)
      ·
        refine ⟨93451912013838734949467405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62301274675892489966311603 93451912013838734949467405)
        ·
          refine ⟨35044467005189525606050277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93451912013838734949467405 35044467005189525606050277)
          ·
            refine ⟨6570837563473036051134427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35044467005189525606050277 6570837563473036051134427)
            ·
              refine ⟨9856256345209554076701641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570837563473036051134427 9856256345209554076701641)
              ·
                refine ⟨7392192258907165557526231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9856256345209554076701641 7392192258907165557526231)
                ·
                  refine ⟨11088288388360748336289347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7392192258907165557526231 11088288388360748336289347)
                  ·
                    refine ⟨16632432582541122504434021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11088288388360748336289347 16632432582541122504434021)
                    ·
                      refine ⟨3118581109226460469581379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16632432582541122504434021 3118581109226460469581379)
                      ·
                        rfl

theorem cell23_6073415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_6073415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073415 prefixEnd_6073415 := by exact prefixLift 6073415
  have htrace : WordTrace (prefixWord ++ tailWord_6073415) baseStart_6073415 baseEnd_6073415 := by
    simpa [prefixWord, tailWord_6073415, baseEnd_6073415] using wordTrace_append hprefix tailTrace_6073415
  have hstable : (prefixWord ++ tailWord_6073415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073415).length < 2 ^ (prefixWord ++ tailWord_6073415).sum := by decide
  have hdescent : baseEnd_6073415 < baseStart_6073415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073432 : List Nat := [2, 1, 2, 2, 1, 3, 2, 5, 1, 2, 2]
def baseStart_6073432 : Nat := 118140960795 + 6073432 * 2 ^ 59
def prefixEnd_6073432 : Nat := 4983230072969 + 3 ^ 40 * 6073432 * 2
def baseEnd_6073432 : Nat := 3118589838397586903068801

theorem tailTrace_6073432 : CollatzResearch.WordTrace tailWord_6073432 prefixEnd_6073432 3118589838397586903068801 := by
  unfold tailWord_6073432
  simp only [CollatzResearch.WordTrace]
  refine ⟨110758131666500299225127275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147677508888667065633503033 110758131666500299225127275)
  ·
    refine ⟨166137197499750448837690913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110758131666500299225127275 166137197499750448837690913)
    ·
      refine ⟨124602898124812836628268185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166137197499750448837690913 124602898124812836628268185)
      ·
        refine ⟨93452173593609627471201139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124602898124812836628268185 93452173593609627471201139)
        ·
          refine ⟨140178260390414441206801709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93452173593609627471201139 140178260390414441206801709)
          ·
            refine ⟨52566847646405415452550641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140178260390414441206801709 52566847646405415452550641)
            ·
              refine ⟨39425135734804061589412981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52566847646405415452550641 39425135734804061589412981)
              ·
                refine ⟨3696106475137880774007467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39425135734804061589412981 3696106475137880774007467)
                ·
                  refine ⟨5544159712706821161011201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696106475137880774007467 5544159712706821161011201)
                  ·
                    refine ⟨4158119784530115870758401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5544159712706821161011201 4158119784530115870758401)
                    ·
                      refine ⟨3118589838397586903068801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158119784530115870758401 3118589838397586903068801)
                      ·
                        rfl

theorem cell23_6073432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_6073432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073432 prefixEnd_6073432 := by exact prefixLift 6073432
  have htrace : WordTrace (prefixWord ++ tailWord_6073432) baseStart_6073432 baseEnd_6073432 := by
    simpa [prefixWord, tailWord_6073432, baseEnd_6073432] using wordTrace_append hprefix tailTrace_6073432
  have hstable : (prefixWord ++ tailWord_6073432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073432).length < 2 ^ (prefixWord ++ tailWord_6073432).sum := by decide
  have hdescent : baseEnd_6073432 < baseStart_6073432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073442 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6073442 : Nat := 118140960795 + 6073442 * 2 ^ 59
def prefixEnd_6073442 : Nat := 4983230072969 + 3 ^ 40 * 6073442 * 2
def baseEnd_6073442 : Nat := 1039531657734710621314585

theorem tailTrace_6073442 : CollatzResearch.WordTrace tailWord_6073442 prefixEnd_6073442 1039531657734710621314585 := by
  unfold tailWord_6073442
  simp only [CollatzResearch.WordTrace]
  refine ⟨55379157015741092539529645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147677752041976246772079053 55379157015741092539529645)
  ·
    refine ⟨20767183880902909702323617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55379157015741092539529645 20767183880902909702323617)
    ·
      refine ⟨15575387910677182276742713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20767183880902909702323617 15575387910677182276742713)
      ·
        refine ⟨11681540933007886707557035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15575387910677182276742713 11681540933007886707557035)
        ·
          refine ⟨17522311399511830061335553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11681540933007886707557035 17522311399511830061335553)
          ·
            refine ⟨13141733549633872546001665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17522311399511830061335553 13141733549633872546001665)
            ·
              refine ⟨9856300162225404409501249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13141733549633872546001665 9856300162225404409501249)
              ·
                refine ⟨7392225121669053307125937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9856300162225404409501249 7392225121669053307125937)
                ·
                  refine ⟨5544168841251789980344453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7392225121669053307125937 5544168841251789980344453)
                  ·
                    refine ⟨1039531657734710621314585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544168841251789980344453 1039531657734710621314585)
                    ·
                      rfl

theorem cell23_6073442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6073442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073442 prefixEnd_6073442 := by exact prefixLift 6073442
  have htrace : WordTrace (prefixWord ++ tailWord_6073442) baseStart_6073442 baseEnd_6073442 := by
    simpa [prefixWord, tailWord_6073442, baseEnd_6073442] using wordTrace_append hprefix tailTrace_6073442
  have hstable : (prefixWord ++ tailWord_6073442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073442).length < 2 ^ (prefixWord ++ tailWord_6073442).sum := by decide
  have hdescent : baseEnd_6073442 < baseStart_6073442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073449 : List Nat := [1, 2, 1, 1, 1, 6, 4, 2, 1, 2, 2]
def baseStart_6073449 : Nat := 118140960795 + 6073449 * 2 ^ 59
def prefixEnd_6073449 : Nat := 4983230072969 + 3 ^ 40 * 6073449 * 2
def baseEnd_6073449 : Nat := 3118598567568713336556223

theorem tailTrace_6073449 : CollatzResearch.WordTrace tailWord_6073449 prefixEnd_6073449 3118598567568713336556223 := by
  unfold tailWord_6073449
  simp only [CollatzResearch.WordTrace]
  refine ⟨221516883373939010353623401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147677922249292673569082267 221516883373939010353623401)
  ·
    refine ⟨166137662530454257765217551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221516883373939010353623401 166137662530454257765217551)
    ·
      refine ⟨249206493795681386647826327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166137662530454257765217551 249206493795681386647826327)
      ·
        refine ⟨373809740693522079971739491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249206493795681386647826327 373809740693522079971739491)
        ·
          refine ⟨560714611040283119957609237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373809740693522079971739491 560714611040283119957609237)
          ·
            refine ⟨26283497392513271248012933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 560714611040283119957609237 26283497392513271248012933)
            ·
              refine ⟨4928155761096238359002425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26283497392513271248012933 4928155761096238359002425)
              ·
                refine ⟨3696116820822178769251819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928155761096238359002425 3696116820822178769251819)
                ·
                  refine ⟨5544175231233268153877729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696116820822178769251819 5544175231233268153877729)
                  ·
                    refine ⟨4158131423424951115408297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5544175231233268153877729 4158131423424951115408297)
                    ·
                      refine ⟨3118598567568713336556223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158131423424951115408297 3118598567568713336556223)
                      ·
                        rfl

theorem cell23_6073449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 2, 1, 2, 2].length) (baseStart_6073449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073449 prefixEnd_6073449 := by exact prefixLift 6073449
  have htrace : WordTrace (prefixWord ++ tailWord_6073449) baseStart_6073449 baseEnd_6073449 := by
    simpa [prefixWord, tailWord_6073449, baseEnd_6073449] using wordTrace_append hprefix tailTrace_6073449
  have hstable : (prefixWord ++ tailWord_6073449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073449).length < 2 ^ (prefixWord ++ tailWord_6073449).sum := by decide
  have hdescent : baseEnd_6073449 < baseStart_6073449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073465 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 3]
def baseStart_6073465 : Nat := 118140960795 + 6073465 * 2 ^ 59
def prefixEnd_6073465 : Nat := 4983230072969 + 3 ^ 40 * 6073465 * 2
def baseEnd_6073465 : Nat := 3118606783259185273956149

theorem tailTrace_6073465 : CollatzResearch.WordTrace tailWord_6073465 prefixEnd_6073465 3118606783259185273956149 := by
  unfold tailWord_6073465
  simp only [CollatzResearch.WordTrace]
  refine ⟨221517466941881045086205849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147678311294587363390803899 221517466941881045086205849)
  ·
    refine ⟨166138100206410783814654387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221517466941881045086205849 166138100206410783814654387)
    ·
      refine ⟨249207150309616175721981581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166138100206410783814654387 249207150309616175721981581)
      ·
        refine ⟨93452681366106065895743093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249207150309616175721981581 93452681366106065895743093)
        ·
          refine ⟨8761188878072443677725915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93452681366106065895743093 8761188878072443677725915)
          ·
            refine ⟨13141783317108665516588873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8761188878072443677725915 13141783317108665516588873)
            ·
              refine ⟨9856337487831499137441655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13141783317108665516588873 9856337487831499137441655)
              ·
                refine ⟨14784506231747248706162483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9856337487831499137441655 14784506231747248706162483)
                ·
                  refine ⟨22176759347620873059243725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14784506231747248706162483 22176759347620873059243725)
                  ·
                    refine ⟨8316284755357827397216397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22176759347620873059243725 8316284755357827397216397)
                    ·
                      refine ⟨3118606783259185273956149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8316284755357827397216397 3118606783259185273956149)
                      ·
                        rfl

theorem cell23_6073465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_6073465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073465 prefixEnd_6073465 := by exact prefixLift 6073465
  have htrace : WordTrace (prefixWord ++ tailWord_6073465) baseStart_6073465 baseEnd_6073465 := by
    simpa [prefixWord, tailWord_6073465, baseEnd_6073465] using wordTrace_append hprefix tailTrace_6073465
  have hstable : (prefixWord ++ tailWord_6073465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073465).length < 2 ^ (prefixWord ++ tailWord_6073465).sum := by decide
  have hdescent : baseEnd_6073465 < baseStart_6073465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073475 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 1, 3, 2]
def baseStart_6073475 : Nat := 118140960795 + 6073475 * 2 ^ 59
def prefixEnd_6073475 : Nat := 4983230072969 + 3 ^ 40 * 6073475 * 2
def baseEnd_6073475 : Nat := 3118611918065730234831103

theorem tailTrace_6073475 : CollatzResearch.WordTrace tailWord_6073475 prefixEnd_6073475 3118611918065730234831103 := by
  unfold tailWord_6073475
  simp only [CollatzResearch.WordTrace]
  refine ⟨221517831671844816794069879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147678554447896544529379919 221517831671844816794069879)
  ·
    refine ⟨332276747507767225191104819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221517831671844816794069879 332276747507767225191104819)
    ·
      refine ⟨498415121261650837786657229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332276747507767225191104819 498415121261650837786657229)
      ·
        refine ⟨186905670473119064169996461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498415121261650837786657229 186905670473119064169996461)
        ·
          refine ⟨70089626427419649063748673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 186905670473119064169996461 70089626427419649063748673)
          ·
            refine ⟨52567219820564736797811505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70089626427419649063748673 52567219820564736797811505)
            ·
              refine ⟨39425414865423552598358629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52567219820564736797811505 39425414865423552598358629)
              ·
                refine ⟨7392265287266916112192243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39425414865423552598358629 7392265287266916112192243)
                ·
                  refine ⟨11088397930900374168288365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7392265287266916112192243 11088397930900374168288365)
                  ·
                    refine ⟨4158149224087640313108137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11088397930900374168288365 4158149224087640313108137)
                    ·
                      refine ⟨3118611918065730234831103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158149224087640313108137 3118611918065730234831103)
                      ·
                        rfl

theorem cell23_6073475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_6073475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073475 prefixEnd_6073475 := by exact prefixLift 6073475
  have htrace : WordTrace (prefixWord ++ tailWord_6073475) baseStart_6073475 baseEnd_6073475 := by
    simpa [prefixWord, tailWord_6073475, baseEnd_6073475] using wordTrace_append hprefix tailTrace_6073475
  have hstable : (prefixWord ++ tailWord_6073475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073475).length < 2 ^ (prefixWord ++ tailWord_6073475).sum := by decide
  have hdescent : baseEnd_6073475 < baseStart_6073475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073488 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 3, 4, 2]
def baseStart_6073488 : Nat := 118140960795 + 6073488 * 2 ^ 59
def prefixEnd_6073488 : Nat := 4983230072969 + 3 ^ 40 * 6073488 * 2
def baseEnd_6073488 : Nat := 3118618593314238683968543

theorem tailTrace_6073488 : CollatzResearch.WordTrace tailWord_6073488 prefixEnd_6073488 3118618593314238683968543 := by
  unfold tailWord_6073488
  simp only [CollatzResearch.WordTrace]
  refine ⟨110759152910398860007146559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147678870547198480009528745 110759152910398860007146559)
  ·
    refine ⟨166138729365598290010719839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110759152910398860007146559 166138729365598290010719839)
    ·
      refine ⟨249208094048397435016079759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166138729365598290010719839 249208094048397435016079759)
      ·
        refine ⟨373812141072596152524119639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249208094048397435016079759 373812141072596152524119639)
        ·
          refine ⟨560718211608894228786179459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373812141072596152524119639 560718211608894228786179459)
          ·
            refine ⟨841077317413341343179269189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560718211608894228786179459 841077317413341343179269189)
            ·
              refine ⟨157701997015001501846112973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 841077317413341343179269189 157701997015001501846112973)
              ·
                refine ⟨59138248880625563192292365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157701997015001501846112973 59138248880625563192292365)
                ·
                  refine ⟨22176843330234586197109637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59138248880625563192292365 22176843330234586197109637)
                  ·
                    refine ⟨4158158124418984911958057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22176843330234586197109637 4158158124418984911958057)
                    ·
                      refine ⟨3118618593314238683968543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158158124418984911958057 3118618593314238683968543)
                      ·
                        rfl

theorem cell23_6073488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 4, 2].length) (baseStart_6073488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073488 prefixEnd_6073488 := by exact prefixLift 6073488
  have htrace : WordTrace (prefixWord ++ tailWord_6073488) baseStart_6073488 baseEnd_6073488 := by
    simpa [prefixWord, tailWord_6073488, baseEnd_6073488] using wordTrace_append hprefix tailTrace_6073488
  have hstable : (prefixWord ++ tailWord_6073488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073488).length < 2 ^ (prefixWord ++ tailWord_6073488).sum := by decide
  have hdescent : baseEnd_6073488 < baseStart_6073488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073491 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5]
def baseStart_6073491 : Nat := 118140960795 + 6073491 * 2 ^ 59
def prefixEnd_6073491 : Nat := 4983230072969 + 3 ^ 40 * 6073491 * 2
def baseEnd_6073491 : Nat := 3118620133756202172231029

theorem tailTrace_6073491 : CollatzResearch.WordTrace tailWord_6073491 prefixEnd_6073491 3118620133756202172231029 := by
  unfold tailWord_6073491
  simp only [CollatzResearch.WordTrace]
  refine ⟨221518415239786851526652327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147678943493191234351101551 221518415239786851526652327)
  ·
    refine ⟨332277622859680277289978491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221518415239786851526652327 332277622859680277289978491)
    ·
      refine ⟨498416434289520415934967737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332277622859680277289978491 498416434289520415934967737)
      ·
        refine ⟨373812325717140311951225803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498416434289520415934967737 373812325717140311951225803)
        ·
          refine ⟨560718488575710467926838705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373812325717140311951225803 560718488575710467926838705)
          ·
            refine ⟨420538866431782850945129029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560718488575710467926838705 420538866431782850945129029)
            ·
              refine ⟨78851037455959284552211693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 420538866431782850945129029 78851037455959284552211693)
              ·
                refine ⟨29569139045984731707079385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78851037455959284552211693 29569139045984731707079385)
                ·
                  refine ⟨22176854284488548780309539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29569139045984731707079385 22176854284488548780309539)
                  ·
                    refine ⟨33265281426732823170464309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22176854284488548780309539 33265281426732823170464309)
                    ·
                      refine ⟨3118620133756202172231029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33265281426732823170464309 3118620133756202172231029)
                      ·
                        rfl

theorem cell23_6073491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_6073491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073491 prefixEnd_6073491 := by exact prefixLift 6073491
  have htrace : WordTrace (prefixWord ++ tailWord_6073491) baseStart_6073491 baseEnd_6073491 := by
    simpa [prefixWord, tailWord_6073491, baseEnd_6073491] using wordTrace_append hprefix tailTrace_6073491
  have hstable : (prefixWord ++ tailWord_6073491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073491).length < 2 ^ (prefixWord ++ tailWord_6073491).sum := by decide
  have hdescent : baseEnd_6073491 < baseStart_6073491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073498 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_6073498 : Nat := 118140960795 + 6073498 * 2 ^ 59
def prefixEnd_6073498 : Nat := 4983230072969 + 3 ^ 40 * 6073498 * 2
def baseEnd_6073498 : Nat := 1039541242706927881614499

theorem tailTrace_6073498 : CollatzResearch.WordTrace tailWord_6073498 prefixEnd_6073498 1039541242706927881614499 := by
  unfold tailWord_6073498
  simp only [CollatzResearch.WordTrace]
  refine ⟨55379667637690372930539287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147679113700507661148104765 55379667637690372930539287)
  ·
    refine ⟨83069501456535559395808931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55379667637690372930539287 83069501456535559395808931)
    ·
      refine ⟨124604252184803339093713397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83069501456535559395808931 124604252184803339093713397)
      ·
        refine ⟨11681648642325313040035631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124604252184803339093713397 11681648642325313040035631)
        ·
          refine ⟨17522472963487969560053447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11681648642325313040035631 17522472963487969560053447)
          ·
            refine ⟨26283709445231954340080171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17522472963487969560053447 26283709445231954340080171)
            ·
              refine ⟨39425564167847931510120257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26283709445231954340080171 39425564167847931510120257)
              ·
                refine ⟨29569173125885948632590193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39425564167847931510120257 29569173125885948632590193)
                ·
                  refine ⟨22176879844414461474442645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29569173125885948632590193 22176879844414461474442645)
                  ·
                    refine ⟨1039541242706927881614499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22176879844414461474442645 1039541242706927881614499)
                    ·
                      rfl

theorem cell23_6073498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_6073498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073498 prefixEnd_6073498 := by exact prefixLift 6073498
  have htrace : WordTrace (prefixWord ++ tailWord_6073498) baseStart_6073498 baseEnd_6073498 := by
    simpa [prefixWord, tailWord_6073498, baseEnd_6073498] using wordTrace_append hprefix tailTrace_6073498
  have hstable : (prefixWord ++ tailWord_6073498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073498).length < 2 ^ (prefixWord ++ tailWord_6073498).sum := by decide
  have hdescent : baseEnd_6073498 < baseStart_6073498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073522 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_6073522 : Nat := 118140960795 + 6073522 * 2 ^ 59
def prefixEnd_6073522 : Nat := 4983230072969 + 3 ^ 40 * 6073522 * 2
def baseEnd_6073522 : Nat := 3118636051656491550943387

theorem tailTrace_6073522 : CollatzResearch.WordTrace tailWord_6073522 prefixEnd_6073522 3118636051656491550943387 := by
  unfold tailWord_6073522
  simp only [CollatzResearch.WordTrace]
  refine ⟨55379886475668635955257705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147679697268449695880687213 55379886475668635955257705)
  ·
    refine ⟨41534914856751476966443279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55379886475668635955257705 41534914856751476966443279)
    ·
      refine ⟨62302372285127215449664919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41534914856751476966443279 62302372285127215449664919)
      ·
        refine ⟨93453558427690823174497379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62302372285127215449664919 93453558427690823174497379)
        ·
          refine ⟨140180337641536234761746069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93453558427690823174497379 140180337641536234761746069)
          ·
            refine ⟨6570953326947011004456847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140180337641536234761746069 6570953326947011004456847)
            ·
              refine ⟨9856429990420516506685271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6570953326947011004456847 9856429990420516506685271)
              ·
                refine ⟨14784644985630774760027907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9856429990420516506685271 14784644985630774760027907)
                ·
                  refine ⟨22176967478446162140041861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14784644985630774760027907 22176967478446162140041861)
                  ·
                    refine ⟨4158181402208655401257849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22176967478446162140041861 4158181402208655401257849)
                    ·
                      refine ⟨3118636051656491550943387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158181402208655401257849 3118636051656491550943387)
                      ·
                        rfl

theorem cell23_6073522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_6073522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073522 prefixEnd_6073522 := by exact prefixLift 6073522
  have htrace : WordTrace (prefixWord ++ tailWord_6073522) baseStart_6073522 baseEnd_6073522 := by
    simpa [prefixWord, tailWord_6073522, baseEnd_6073522] using wordTrace_append hprefix tailTrace_6073522
  have hstable : (prefixWord ++ tailWord_6073522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073522).length < 2 ^ (prefixWord ++ tailWord_6073522).sum := by decide
  have hdescent : baseEnd_6073522 < baseStart_6073522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073568 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_6073568 : Nat := 118140960795 + 6073568 * 2 ^ 59
def prefixEnd_6073568 : Nat := 4983230072969 + 3 ^ 40 * 6073568 * 2
def baseEnd_6073568 : Nat := 3118659671766598370968175

theorem tailTrace_6073568 : CollatzResearch.WordTrace tailWord_6073568 prefixEnd_6073568 3118659671766598370968175 := by
  unfold tailWord_6073568
  simp only [CollatzResearch.WordTrace]
  refine ⟨110760611830253946838602679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147680815773671929118136905 110760611830253946838602679)
  ·
    refine ⟨166140917745380920257904019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110760611830253946838602679 166140917745380920257904019)
    ·
      refine ⟨249211376618071380386856029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166140917745380920257904019 249211376618071380386856029)
      ·
        refine ⟨93454266231776767645071011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249211376618071380386856029 93454266231776767645071011)
        ·
          refine ⟨140181399347665151467606517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93454266231776767645071011 140181399347665151467606517)
          ·
            refine ⟨13142006188843607950088111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140181399347665151467606517 13142006188843607950088111)
            ·
              refine ⟨19713009283265411925132167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13142006188843607950088111 19713009283265411925132167)
              ·
                refine ⟨29569513924898117887698251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19713009283265411925132167 29569513924898117887698251)
                ·
                  refine ⟨44354270887347176831547377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29569513924898117887698251 44354270887347176831547377)
                  ·
                    refine ⟨33265703165510382623660533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44354270887347176831547377 33265703165510382623660533)
                    ·
                      refine ⟨3118659671766598370968175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33265703165510382623660533 3118659671766598370968175)
                      ·
                        rfl

theorem cell23_6073568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_6073568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073568 prefixEnd_6073568 := by exact prefixLift 6073568
  have htrace : WordTrace (prefixWord ++ tailWord_6073568) baseStart_6073568 baseEnd_6073568 := by
    simpa [prefixWord, tailWord_6073568, baseEnd_6073568] using wordTrace_append hprefix tailTrace_6073568
  have hstable : (prefixWord ++ tailWord_6073568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073568).length < 2 ^ (prefixWord ++ tailWord_6073568).sum := by decide
  have hdescent : baseEnd_6073568 < baseStart_6073568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073573 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 2, 2, 2]
def baseStart_6073573 : Nat := 118140960795 + 6073573 * 2 ^ 59
def prefixEnd_6073573 : Nat := 4983230072969 + 3 ^ 40 * 6073573 * 2
def baseEnd_6073573 : Nat := 3118662239169870851405653

theorem tailTrace_6073573 : CollatzResearch.WordTrace tailWord_6073573 prefixEnd_6073573 3118662239169870851405653 := by
  unfold tailWord_6073573
  simp only [CollatzResearch.WordTrace]
  refine ⟨221521406025489779531137373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147680937350326519687424915 221521406025489779531137373)
  ·
    refine ⟨83070527259558667324176515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221521406025489779531137373 83070527259558667324176515)
    ·
      refine ⟨124605790889338000986264773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83070527259558667324176515 124605790889338000986264773)
      ·
        refine ⟨23363585791750875184924645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124605790889338000986264773 23363585791750875184924645)
        ·
          refine ⟨4380672335953289097173371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23363585791750875184924645 4380672335953289097173371)
          ·
            refine ⟨6571008503929933645760057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4380672335953289097173371 6571008503929933645760057)
            ·
              refine ⟨4928256377947450234320043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571008503929933645760057 4928256377947450234320043)
              ·
                refine ⟨7392384566921175351480065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928256377947450234320043 7392384566921175351480065)
                ·
                  refine ⟨5544288425190881513610049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7392384566921175351480065 5544288425190881513610049)
                  ·
                    refine ⟨4158216318893161135207537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5544288425190881513610049 4158216318893161135207537)
                    ·
                      refine ⟨3118662239169870851405653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158216318893161135207537 3118662239169870851405653)
                      ·
                        rfl

theorem cell23_6073573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_6073573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073573 prefixEnd_6073573 := by exact prefixLift 6073573
  have htrace : WordTrace (prefixWord ++ tailWord_6073573) baseStart_6073573 baseEnd_6073573 := by
    simpa [prefixWord, tailWord_6073573, baseEnd_6073573] using wordTrace_append hprefix tailTrace_6073573
  have hstable : (prefixWord ++ tailWord_6073573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073573).length < 2 ^ (prefixWord ++ tailWord_6073573).sum := by decide
  have hdescent : baseEnd_6073573 < baseStart_6073573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073648 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 3, 5]
def baseStart_6073648 : Nat := 118140960795 + 6073648 * 2 ^ 59
def prefixEnd_6073648 : Nat := 4983230072969 + 3 ^ 40 * 6073648 * 2
def baseEnd_6073648 : Nat := 1039566916739652685989269

theorem tailTrace_6073648 : CollatzResearch.WordTrace tailWord_6073648 prefixEnd_6073648 1039566916739652685989269 := by
  unfold tailWord_6073648
  simp only [CollatzResearch.WordTrace]
  refine ⟨110762070750109033670058799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147682761000145378226745065 110762070750109033670058799)
  ·
    refine ⟨166143106125163550505088199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110762070750109033670058799 166143106125163550505088199)
    ·
      refine ⟨249214659187745325757632299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166143106125163550505088199 249214659187745325757632299)
      ·
        refine ⟨373821988781617988636448449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249214659187745325757632299 373821988781617988636448449)
        ·
          refine ⟨280366491586213491477336337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373821988781617988636448449 280366491586213491477336337)
          ·
            refine ⟨210274868689660118608002253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280366491586213491477336337 210274868689660118608002253)
            ·
              refine ⟨78853075758622544478000845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210274868689660118608002253 78853075758622544478000845)
              ·
                refine ⟨29569903409483454179250317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78853075758622544478000845 29569903409483454179250317)
                ·
                  refine ⟨11088713778556295317218869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29569903409483454179250317 11088713778556295317218869)
                  ·
                    refine ⟨1039566916739652685989269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11088713778556295317218869 1039566916739652685989269)
                    ·
                      rfl

theorem cell23_6073648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_6073648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073648 prefixEnd_6073648 := by exact prefixLift 6073648
  have htrace : WordTrace (prefixWord ++ tailWord_6073648) baseStart_6073648 baseEnd_6073648 := by
    simpa [prefixWord, tailWord_6073648, baseEnd_6073648] using wordTrace_append hprefix tailTrace_6073648
  have hstable : (prefixWord ++ tailWord_6073648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073648).length < 2 ^ (prefixWord ++ tailWord_6073648).sum := by decide
  have hdescent : baseEnd_6073648 < baseStart_6073648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073662 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_6073662 : Nat := 118140960795 + 6073662 * 2 ^ 59
def prefixEnd_6073662 : Nat := 4983230072969 + 3 ^ 40 * 6073662 * 2
def baseEnd_6073662 : Nat := 3118707938948121003192743

theorem tailTrace_6073662 : CollatzResearch.WordTrace tailWord_6073662 prefixEnd_6073662 3118707938948121003192743 := by
  unfold tailWord_6073662
  simp only [CollatzResearch.WordTrace]
  refine ⟨27690581515270918466390905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147683101414778231820751493 27690581515270918466390905)
  ·
    refine ⟨20767936136453188849793179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27690581515270918466390905 20767936136453188849793179)
    ·
      refine ⟨31151904204679783274689769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20767936136453188849793179 31151904204679783274689769)
      ·
        refine ⟨23363928153509837456017327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31151904204679783274689769 23363928153509837456017327)
        ·
          refine ⟨35045892230264756184025991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23363928153509837456017327 35045892230264756184025991)
          ·
            refine ⟨52568838345397134276038987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35045892230264756184025991 52568838345397134276038987)
            ·
              refine ⟨78853257518095701414058481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52568838345397134276038987 78853257518095701414058481)
              ·
                refine ⟨59139943138571776060543861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78853257518095701414058481 59139943138571776060543861)
                ·
                  refine ⟨5544369669241104005675987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59139943138571776060543861 5544369669241104005675987)
                  ·
                    refine ⟨8316554503861656008513981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5544369669241104005675987 8316554503861656008513981)
                    ·
                      refine ⟨3118707938948121003192743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8316554503861656008513981 3118707938948121003192743)
                      ·
                        rfl

theorem cell23_6073662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_6073662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073662 prefixEnd_6073662 := by exact prefixLift 6073662
  have htrace : WordTrace (prefixWord ++ tailWord_6073662) baseStart_6073662 baseEnd_6073662 := by
    simpa [prefixWord, tailWord_6073662, baseEnd_6073662] using wordTrace_append hprefix tailTrace_6073662
  have hstable : (prefixWord ++ tailWord_6073662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073662).length < 2 ^ (prefixWord ++ tailWord_6073662).sum := by decide
  have hdescent : baseEnd_6073662 < baseStart_6073662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073730 : List Nat := [3, 4, 2, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6073730 : Nat := 118140960795 + 6073730 * 2 ^ 59
def prefixEnd_6073730 : Nat := 4983230072969 + 3 ^ 40 * 6073730 * 2
def baseEnd_6073730 : Nat := 3118742855632626737142431

theorem tailTrace_6073730 : CollatzResearch.WordTrace tailWord_6073730 prefixEnd_6073730 3118742855632626737142431 := by
  unfold tailWord_6073730
  simp only [CollatzResearch.WordTrace]
  refine ⟨55381783071480248836150661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147684754857280663563068429 55381783071480248836150661)
  ·
    refine ⟨10384084325902546656778249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55381783071480248836150661 10384084325902546656778249)
    ·
      refine ⟨7788063244426909992583687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10384084325902546656778249 7788063244426909992583687)
      ·
        refine ⟨11682094866640364988875531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7788063244426909992583687 11682094866640364988875531)
        ·
          refine ⟨17523142299960547483313297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11682094866640364988875531 17523142299960547483313297)
          ·
            refine ⟨13142356724970410612484973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17523142299960547483313297 13142356724970410612484973)
            ·
              refine ⟨4928383771863903979681865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13142356724970410612484973 4928383771863903979681865)
              ·
                refine ⟨3696287828897927984761399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928383771863903979681865 3696287828897927984761399)
                ·
                  refine ⟨5544431743346891977142099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696287828897927984761399 5544431743346891977142099)
                  ·
                    refine ⟨8316647615020337965713149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5544431743346891977142099 8316647615020337965713149)
                    ·
                      refine ⟨3118742855632626737142431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8316647615020337965713149 3118742855632626737142431)
                      ·
                        rfl

theorem cell23_6073730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6073730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073730 prefixEnd_6073730 := by exact prefixLift 6073730
  have htrace : WordTrace (prefixWord ++ tailWord_6073730) baseStart_6073730 baseEnd_6073730 := by
    simpa [prefixWord, tailWord_6073730, baseEnd_6073730] using wordTrace_append hprefix tailTrace_6073730
  have hstable : (prefixWord ++ tailWord_6073730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073730).length < 2 ^ (prefixWord ++ tailWord_6073730).sum := by decide
  have hdescent : baseEnd_6073730 < baseStart_6073730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073736 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_6073736 : Nat := 118140960795 + 6073736 * 2 ^ 59
def prefixEnd_6073736 : Nat := 4983230072969 + 3 ^ 40 * 6073736 * 2
def baseEnd_6073736 : Nat := 3118745936516553713667403

theorem tailTrace_6073736 : CollatzResearch.WordTrace tailWord_6073736 prefixEnd_6073736 3118745936516553713667403 := by
  unfold tailWord_6073736
  simp only [CollatzResearch.WordTrace]
  refine ⟨110763675561949629184660531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147684900749266172246214041 110763675561949629184660531)
  ·
    refine ⟨166145513342924443776990797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110763675561949629184660531 166145513342924443776990797)
    ·
      refine ⟨62304567503596666416371549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166145513342924443776990797 62304567503596666416371549)
      ·
        refine ⟨23364212813848749906139331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62304567503596666416371549 23364212813848749906139331)
        ·
          refine ⟨35046319220773124859208997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23364212813848749906139331 35046319220773124859208997)
          ·
            refine ⟨6571184853894960911101687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35046319220773124859208997 6571184853894960911101687)
            ·
              refine ⟨9856777280842441366652531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571184853894960911101687 9856777280842441366652531)
              ·
                refine ⟨14785165921263662049978797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9856777280842441366652531 14785165921263662049978797)
                ·
                  refine ⟨5544437220473873268742049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14785165921263662049978797 5544437220473873268742049)
                  ·
                    refine ⟨4158327915355404951556537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5544437220473873268742049 4158327915355404951556537)
                    ·
                      refine ⟨3118745936516553713667403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158327915355404951556537 3118745936516553713667403)
                      ·
                        rfl

theorem cell23_6073736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_6073736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073736 prefixEnd_6073736 := by exact prefixLift 6073736
  have htrace : WordTrace (prefixWord ++ tailWord_6073736) baseStart_6073736 baseEnd_6073736 := by
    simpa [prefixWord, tailWord_6073736, baseEnd_6073736] using wordTrace_append hprefix tailTrace_6073736
  have hstable : (prefixWord ++ tailWord_6073736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073736).length < 2 ^ (prefixWord ++ tailWord_6073736).sum := by decide
  have hdescent : baseEnd_6073736 < baseStart_6073736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073742 : List Nat := [4, 1, 1, 4, 2, 1, 2, 8]
def baseStart_6073742 : Nat := 118140960795 + 6073742 * 2 ^ 59
def prefixEnd_6073742 : Nat := 4983230072969 + 3 ^ 40 * 6073742 * 2
def baseEnd_6073742 : Nat := 115509222866684470007125

theorem tailTrace_6073742 : CollatzResearch.WordTrace tailWord_6073742 prefixEnd_6073742 115509222866684470007125 := by
  unfold tailWord_6073742
  simp only [CollatzResearch.WordTrace]
  refine ⟨27690946245234690174254935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147685046641251680929359653 27690946245234690174254935)
  ·
    refine ⟨41536419367852035261382403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27690946245234690174254935 41536419367852035261382403)
    ·
      refine ⟨62304629051778052892073605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41536419367852035261382403 62304629051778052892073605)
      ·
        refine ⟨11682117947208384917263801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62304629051778052892073605 11682117947208384917263801)
        ·
          refine ⟨8761588460406288687947851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11682117947208384917263801 8761588460406288687947851)
          ·
            refine ⟨13142382690609433031921777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8761588460406288687947851 13142382690609433031921777)
            ·
              refine ⟨9856787017957074773941333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13142382690609433031921777 9856787017957074773941333)
              ·
                refine ⟨115509222866684470007125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9856787017957074773941333 115509222866684470007125)
                ·
                  rfl

theorem cell23_6073742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_6073742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073742 prefixEnd_6073742 := by exact prefixLift 6073742
  have htrace : WordTrace (prefixWord ++ tailWord_6073742) baseStart_6073742 baseEnd_6073742 := by
    simpa [prefixWord, tailWord_6073742, baseEnd_6073742] using wordTrace_append hprefix tailTrace_6073742
  have hstable : (prefixWord ++ tailWord_6073742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073742).length < 2 ^ (prefixWord ++ tailWord_6073742).sum := by decide
  have hdescent : baseEnd_6073742 < baseStart_6073742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073746 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_6073746 : Nat := 118140960795 + 6073746 * 2 ^ 59
def prefixEnd_6073746 : Nat := 4983230072969 + 3 ^ 40 * 6073746 * 2
def baseEnd_6073746 : Nat := 1039583690441032891514119

theorem tailTrace_6073746 : CollatzResearch.WordTrace tailWord_6073746 prefixEnd_6073746 1039583690441032891514119 := by
  unfold tailWord_6073746
  simp only [CollatzResearch.WordTrace]
  refine ⟨55381928963465757519296273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147685143902575353384790061 55381928963465757519296273)
  ·
    refine ⟨41536446722599318139472205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55381928963465757519296273 41536446722599318139472205)
    ·
      refine ⟨15576167520974744302302077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41536446722599318139472205 15576167520974744302302077)
      ·
        refine ⟨5841062820365529113363279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15576167520974744302302077 5841062820365529113363279)
        ·
          refine ⟨8761594230548293670044919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841062820365529113363279 8761594230548293670044919)
          ·
            refine ⟨13142391345822440505067379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8761594230548293670044919 13142391345822440505067379)
            ·
              refine ⟨19713587018733660757601069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13142391345822440505067379 19713587018733660757601069)
              ·
                refine ⟨7392595132025122784100401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19713587018733660757601069 7392595132025122784100401)
                ·
                  refine ⟨5544446349018842088075301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7392595132025122784100401 5544446349018842088075301)
                  ·
                    refine ⟨1039583690441032891514119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544446349018842088075301 1039583690441032891514119)
                    ·
                      rfl

theorem cell23_6073746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_6073746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073746 prefixEnd_6073746 := by exact prefixLift 6073746
  have htrace : WordTrace (prefixWord ++ tailWord_6073746) baseStart_6073746 baseEnd_6073746 := by
    simpa [prefixWord, tailWord_6073746, baseEnd_6073746] using wordTrace_append hprefix tailTrace_6073746
  have hstable : (prefixWord ++ tailWord_6073746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073746).length < 2 ^ (prefixWord ++ tailWord_6073746).sum := by decide
  have hdescent : baseEnd_6073746 < baseStart_6073746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073795 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 3]
def baseStart_6073795 : Nat := 118140960795 + 6073795 * 2 ^ 59
def prefixEnd_6073795 : Nat := 4983230072969 + 3 ^ 40 * 6073795 * 2
def baseEnd_6073795 : Nat := 3118776231875168982829631

theorem tailTrace_6073795 : CollatzResearch.WordTrace tailWord_6073795 prefixEnd_6073795 3118776231875168982829631 := by
  unfold tailWord_6073795
  simp only [CollatzResearch.WordTrace]
  refine ⟨221529503030685511445718839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147686335353790340963812559 221529503030685511445718839)
  ·
    refine ⟨332294254546028267168578259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221529503030685511445718839 332294254546028267168578259)
    ·
      refine ⟨498441381819042400752867389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332294254546028267168578259 498441381819042400752867389)
      ·
        refine ⟨186915518182140900282325271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 498441381819042400752867389 186915518182140900282325271)
        ·
          refine ⟨280373277273211350423487907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186915518182140900282325271 280373277273211350423487907)
          ·
            refine ⟨420559915909817025635231861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280373277273211350423487907 420559915909817025635231861)
            ·
              refine ⟨39427492116545346153302987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 420559915909817025635231861 39427492116545346153302987)
              ·
                refine ⟨59141238174818019229954481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39427492116545346153302987 59141238174818019229954481)
                ·
                  refine ⟨44355928631113514422465861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59141238174818019229954481 44355928631113514422465861)
                  ·
                    refine ⟨8316736618333783954212349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44355928631113514422465861 8316736618333783954212349)
                    ·
                      refine ⟨3118776231875168982829631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8316736618333783954212349 3118776231875168982829631)
                      ·
                        rfl

theorem cell23_6073795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_6073795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073795 prefixEnd_6073795 := by exact prefixLift 6073795
  have htrace : WordTrace (prefixWord ++ tailWord_6073795) baseStart_6073795 baseEnd_6073795 := by
    simpa [prefixWord, tailWord_6073795, baseEnd_6073795] using wordTrace_append hprefix tailTrace_6073795
  have hstable : (prefixWord ++ tailWord_6073795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073795).length < 2 ^ (prefixWord ++ tailWord_6073795).sum := by decide
  have hdescent : baseEnd_6073795 < baseStart_6073795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073852 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_6073852 : Nat := 118140960795 + 6073852 * 2 ^ 59
def prefixEnd_6073852 : Nat := 4983230072969 + 3 ^ 40 * 6073852 * 2
def baseEnd_6073852 : Nat := 3118805500272475259816869

theorem tailTrace_6073852 : CollatzResearch.WordTrace tailWord_6073852 prefixEnd_6073852 3118805500272475259816869 := by
  unfold tailWord_6073852
  simp only [CollatzResearch.WordTrace]
  refine ⟨110765790995739505090271905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147687721327652673453695873 110765790995739505090271905)
  ·
    refine ⟨83074343246804628817703929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110765790995739505090271905 83074343246804628817703929)
    ·
      refine ⟨62305757435103471613277947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83074343246804628817703929 62305757435103471613277947)
      ·
        refine ⟨93458636152655207419916921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62305757435103471613277947 93458636152655207419916921)
        ·
          refine ⟨70093977114491405564937691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93458636152655207419916921 70093977114491405564937691)
          ·
            refine ⟨105140965671737108347406537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70093977114491405564937691 105140965671737108347406537)
            ·
              refine ⟨78855724253802831260554903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105140965671737108347406537 78855724253802831260554903)
              ·
                refine ⟨118283586380704246890832355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78855724253802831260554903 118283586380704246890832355)
                ·
                  refine ⟨177425379571056370336248533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118283586380704246890832355 177425379571056370336248533)
                  ·
                    refine ⟨4158407333696633679755825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 177425379571056370336248533 4158407333696633679755825)
                    ·
                      refine ⟨3118805500272475259816869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158407333696633679755825 3118805500272475259816869)
                      ·
                        rfl

theorem cell23_6073852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_6073852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073852 prefixEnd_6073852 := by exact prefixLift 6073852
  have htrace : WordTrace (prefixWord ++ tailWord_6073852) baseStart_6073852 baseEnd_6073852 := by
    simpa [prefixWord, tailWord_6073852, baseEnd_6073852] using wordTrace_append hprefix tailTrace_6073852
  have hstable : (prefixWord ++ tailWord_6073852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073852).length < 2 ^ (prefixWord ++ tailWord_6073852).sum := by decide
  have hdescent : baseEnd_6073852 < baseStart_6073852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073860 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6073860 : Nat := 118140960795 + 6073860 * 2 ^ 59
def prefixEnd_6073860 : Nat := 4983230072969 + 3 ^ 40 * 6073860 * 2
def baseEnd_6073860 : Nat := 3118809608117711228516833

theorem tailTrace_6073860 : CollatzResearch.WordTrace tailWord_6073860 prefixEnd_6073860 3118809608117711228516833 := by
  unfold tailWord_6073860
  simp only [CollatzResearch.WordTrace]
  refine ⟨110765936887725013773417517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147687915850300018364556689 110765936887725013773417517)
  ·
    refine ⟨41537226332896880165031569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110765936887725013773417517 41537226332896880165031569)
    ·
      refine ⟨31152919749672660123773677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41537226332896880165031569 31152919749672660123773677)
      ·
        refine ⟨11682344906127247546415129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31152919749672660123773677 11682344906127247546415129)
        ·
          refine ⟨8761758679595435659811347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11682344906127247546415129 8761758679595435659811347)
          ·
            refine ⟨13142638019393153489717021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8761758679595435659811347 13142638019393153489717021)
            ·
              refine ⟨4928489257272432558643883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13142638019393153489717021 4928489257272432558643883)
              ·
                refine ⟨7392733885908648837965825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928489257272432558643883 7392733885908648837965825)
                ·
                  refine ⟨5544550414431486628474369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7392733885908648837965825 5544550414431486628474369)
                  ·
                    refine ⟨4158412810823614971355777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5544550414431486628474369 4158412810823614971355777)
                    ·
                      refine ⟨3118809608117711228516833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158412810823614971355777 3118809608117711228516833)
                      ·
                        rfl

theorem cell23_6073860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6073860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073860 prefixEnd_6073860 := by exact prefixLift 6073860
  have htrace : WordTrace (prefixWord ++ tailWord_6073860) baseStart_6073860 baseEnd_6073860 := by
    simpa [prefixWord, tailWord_6073860, baseEnd_6073860] using wordTrace_append hprefix tailTrace_6073860
  have hstable : (prefixWord ++ tailWord_6073860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073860).length < 2 ^ (prefixWord ++ tailWord_6073860).sum := by decide
  have hdescent : baseEnd_6073860 < baseStart_6073860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073865 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_6073865 : Nat := 118140960795 + 6073865 * 2 ^ 59
def prefixEnd_6073865 : Nat := 4983230072969 + 3 ^ 40 * 6073865 * 2
def baseEnd_6073865 : Nat := 3118812175520983708954309

theorem tailTrace_6073865 : CollatzResearch.WordTrace tailWord_6073865 prefixEnd_6073865 3118812175520983708954309 := by
  unfold tailWord_6073865
  simp only [CollatzResearch.WordTrace]
  refine ⟨221532056140431913400767049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147688037426954608933844699 221532056140431913400767049)
  ·
    refine ⟨166149042105323935050575287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221532056140431913400767049 166149042105323935050575287)
    ·
      refine ⟨249223563157985902575862931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166149042105323935050575287 249223563157985902575862931)
      ·
        refine ⟨373835344736978853863794397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249223563157985902575862931 373835344736978853863794397)
        ·
          refine ⟨140188254276367070198922899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373835344736978853863794397 140188254276367070198922899)
          ·
            refine ⟨210282381414550605298384349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140188254276367070198922899 210282381414550605298384349)
            ·
              refine ⟨78855893030456476986894131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210282381414550605298384349 78855893030456476986894131)
              ·
                refine ⟨118283839545684715480341197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78855893030456476986894131 118283839545684715480341197)
                ·
                  refine ⟨44356439829631768305127949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118283839545684715480341197 44356439829631768305127949)
                  ·
                    refine ⟨16633664936111913114422981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44356439829631768305127949 16633664936111913114422981)
                    ·
                      refine ⟨3118812175520983708954309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16633664936111913114422981 3118812175520983708954309)
                      ·
                        rfl

theorem cell23_6073865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_6073865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073865 prefixEnd_6073865 := by exact prefixLift 6073865
  have htrace : WordTrace (prefixWord ++ tailWord_6073865) baseStart_6073865 baseEnd_6073865 := by
    simpa [prefixWord, tailWord_6073865, baseEnd_6073865] using wordTrace_append hprefix tailTrace_6073865
  have hstable : (prefixWord ++ tailWord_6073865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073865).length < 2 ^ (prefixWord ++ tailWord_6073865).sum := by decide
  have hdescent : baseEnd_6073865 < baseStart_6073865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073882 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_6073882 : Nat := 118140960795 + 6073882 * 2 ^ 59
def prefixEnd_6073882 : Nat := 4983230072969 + 3 ^ 40 * 6073882 * 2
def baseEnd_6073882 : Nat := 3118820904692110142441731

theorem tailTrace_6073882 : CollatzResearch.WordTrace tailWord_6073882 prefixEnd_6073882 3118820904692110142441731 := by
  unfold tailWord_6073882
  simp only [CollatzResearch.WordTrace]
  refine ⟨55383169045342581326033975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147688450787580216869423933 55383169045342581326033975)
  ·
    refine ⟨83074753568013871989050963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55383169045342581326033975 83074753568013871989050963)
    ·
      refine ⟨124612130352020807983576445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83074753568013871989050963 124612130352020807983576445)
      ·
        refine ⟨46729548882007802993841167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124612130352020807983576445 46729548882007802993841167)
        ·
          refine ⟨70094323323011704490761751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46729548882007802993841167 70094323323011704490761751)
          ·
            refine ⟨105141484984517556736142627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70094323323011704490761751 105141484984517556736142627)
            ·
              refine ⟨157712227476776335104213941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105141484984517556736142627 157712227476776335104213941)
              ·
                refine ⟨14785521325947781416020057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157712227476776335104213941 14785521325947781416020057)
                ·
                  refine ⟨11089140994460836062015043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14785521325947781416020057 11089140994460836062015043)
                  ·
                    refine ⟨16633711491691254093022565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11089140994460836062015043 16633711491691254093022565)
                    ·
                      refine ⟨3118820904692110142441731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16633711491691254093022565 3118820904692110142441731)
                      ·
                        rfl

theorem cell23_6073882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_6073882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073882 prefixEnd_6073882 := by exact prefixLift 6073882
  have htrace : WordTrace (prefixWord ++ tailWord_6073882) baseStart_6073882 baseEnd_6073882 := by
    simpa [prefixWord, tailWord_6073882, baseEnd_6073882] using wordTrace_append hprefix tailTrace_6073882
  have hstable : (prefixWord ++ tailWord_6073882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073882).length < 2 ^ (prefixWord ++ tailWord_6073882).sum := by decide
  have hdescent : baseEnd_6073882 < baseStart_6073882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073909 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_6073909 : Nat := 118140960795 + 6073909 * 2 ^ 59
def prefixEnd_6073909 : Nat := 4983230072969 + 3 ^ 40 * 6073909 * 2
def baseEnd_6073909 : Nat := 1039611589556593845601369

theorem tailTrace_6073909 : CollatzResearch.WordTrace tailWord_6073909 prefixEnd_6073909 1039611589556593845601369 := by
  unfold tailWord_6073909
  simp only [CollatzResearch.WordTrace]
  refine ⟨221533660952272508915368781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147689107301515005943579187 221533660952272508915368781)
  ·
    refine ⟨83075122857102190843263293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221533660952272508915368781 83075122857102190843263293)
    ·
      refine ⟨31153171071413321566223735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83075122857102190843263293 31153171071413321566223735)
      ·
        refine ⟨46729756607119982349335603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31153171071413321566223735 46729756607119982349335603)
        ·
          refine ⟨70094634910679973524003405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46729756607119982349335603 70094634910679973524003405)
          ·
            refine ⟨26285488091504990071501277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70094634910679973524003405 26285488091504990071501277)
            ·
              refine ⟨9857058034314371276812979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26285488091504990071501277 9857058034314371276812979)
              ·
                refine ⟨14785587051471556915219469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9857058034314371276812979 14785587051471556915219469)
                ·
                  refine ⟨5544595144301833843207301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14785587051471556915219469 5544595144301833843207301)
                  ·
                    refine ⟨1039611589556593845601369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544595144301833843207301 1039611589556593845601369)
                    ·
                      rfl

theorem cell23_6073909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_6073909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073909 prefixEnd_6073909 := by exact prefixLift 6073909
  have htrace : WordTrace (prefixWord ++ tailWord_6073909) baseStart_6073909 baseEnd_6073909 := by
    simpa [prefixWord, tailWord_6073909, baseEnd_6073909] using wordTrace_append hprefix tailTrace_6073909
  have hstable : (prefixWord ++ tailWord_6073909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073909).length < 2 ^ (prefixWord ++ tailWord_6073909).sum := by decide
  have hdescent : baseEnd_6073909 < baseStart_6073909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073945 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_6073945 : Nat := 118140960795 + 6073945 * 2 ^ 59
def prefixEnd_6073945 : Nat := 4983230072969 + 3 ^ 40 * 6073945 * 2
def baseEnd_6073945 : Nat := 3118853253973343395953941

theorem tailTrace_6073945 : CollatzResearch.WordTrace tailWord_6073945 prefixEnd_6073945 3118853253973343395953941 := by
  unfold tailWord_6073945
  simp only [CollatzResearch.WordTrace]
  refine ⟨221534973980142087063679289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147689982653428058042452859 221534973980142087063679289)
  ·
    refine ⟨166151230485106565297759467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221534973980142087063679289 166151230485106565297759467)
    ·
      refine ⟨249226845727659847946639201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166151230485106565297759467 249226845727659847946639201)
      ·
        refine ⟨186920134295744885959979401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249226845727659847946639201 186920134295744885959979401)
        ·
          refine ⟨140190100721808664469984551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186920134295744885959979401 140190100721808664469984551)
          ·
            refine ⟨210285151082712996704976827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140190100721808664469984551 210285151082712996704976827)
            ·
              refine ⟨315427726624069495057465241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210285151082712996704976827 315427726624069495057465241)
              ·
                refine ⟨236570794968052121293098931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315427726624069495057465241 236570794968052121293098931)
                ·
                  refine ⟨354856192452078181939648397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236570794968052121293098931 354856192452078181939648397)
                  ·
                    refine ⟨133071072169529318227368149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354856192452078181939648397 133071072169529318227368149)
                    ·
                      refine ⟨3118853253973343395953941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133071072169529318227368149 3118853253973343395953941)
                      ·
                        rfl

theorem cell23_6073945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_6073945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073945 prefixEnd_6073945 := by exact prefixLift 6073945
  have htrace : WordTrace (prefixWord ++ tailWord_6073945) baseStart_6073945 baseEnd_6073945 := by
    simpa [prefixWord, tailWord_6073945, baseEnd_6073945] using wordTrace_append hprefix tailTrace_6073945
  have hstable : (prefixWord ++ tailWord_6073945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073945).length < 2 ^ (prefixWord ++ tailWord_6073945).sum := by decide
  have hdescent : baseEnd_6073945 < baseStart_6073945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073960 : List Nat := [2, 1, 4, 3, 1, 3, 2, 2, 1, 4]
def baseStart_6073960 : Nat := 118140960795 + 6073960 * 2 ^ 59
def prefixEnd_6073960 : Nat := 4983230072969 + 3 ^ 40 * 6073960 * 2
def baseEnd_6073960 : Nat := 1039620318727720279088791

theorem tailTrace_6073960 : CollatzResearch.WordTrace tailWord_6073960 prefixEnd_6073960 1039620318727720279088791 := by
  unfold tailWord_6073960
  simp only [CollatzResearch.WordTrace]
  refine ⟨110767760537543872312737667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147690347383391829750316889 110767760537543872312737667)
  ·
    refine ⟨166151640806315808469106501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110767760537543872312737667 166151640806315808469106501)
    ·
      refine ⟨31153432651184214087957469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166151640806315808469106501 31153432651184214087957469)
      ·
        refine ⟨11682537244194080282984051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31153432651184214087957469 11682537244194080282984051)
        ·
          refine ⟨17523805866291120424476077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11682537244194080282984051 17523805866291120424476077)
          ·
            refine ⟨6571427199859170159178529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17523805866291120424476077 6571427199859170159178529)
            ·
              refine ⟨4928570399894377619383897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571427199859170159178529 4928570399894377619383897)
              ·
                refine ⟨3696427799920783214537923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928570399894377619383897 3696427799920783214537923)
                ·
                  refine ⟨5544641699881174821806885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696427799920783214537923 5544641699881174821806885)
                  ·
                    refine ⟨1039620318727720279088791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544641699881174821806885 1039620318727720279088791)
                    ·
                      rfl

theorem cell23_6073960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_6073960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073960 prefixEnd_6073960 := by exact prefixLift 6073960
  have htrace : WordTrace (prefixWord ++ tailWord_6073960) baseStart_6073960 baseEnd_6073960 := by
    simpa [prefixWord, tailWord_6073960, baseEnd_6073960] using wordTrace_append hprefix tailTrace_6073960
  have hstable : (prefixWord ++ tailWord_6073960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073960).length < 2 ^ (prefixWord ++ tailWord_6073960).sum := by decide
  have hdescent : baseEnd_6073960 < baseStart_6073960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6073989 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_6073989 : Nat := 118140960795 + 6073989 * 2 ^ 59
def prefixEnd_6073989 : Nat := 4983230072969 + 3 ^ 40 * 6073989 * 2
def baseEnd_6073989 : Nat := 3118875847122141223803739

theorem tailTrace_6073989 : CollatzResearch.WordTrace tailWord_6073989 prefixEnd_6073989 3118875847122141223803739 := by
  unfold tailWord_6073989
  simp only [CollatzResearch.WordTrace]
  refine ⟨221536578791982682578281021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147691052527988455052187347 221536578791982682578281021)
  ·
    refine ⟨83076217046993505966855383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221536578791982682578281021 83076217046993505966855383)
    ·
      refine ⟨124614325570490258950283075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83076217046993505966855383 124614325570490258950283075)
      ·
        refine ⟨186921488355735388425424613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124614325570490258950283075 186921488355735388425424613)
        ·
          refine ⟨35047779066700385329767115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 186921488355735388425424613 35047779066700385329767115)
          ·
            refine ⟨52571668600050577994650673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35047779066700385329767115 52571668600050577994650673)
            ·
              refine ⟨39428751450037933495988005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52571668600050577994650673 39428751450037933495988005)
              ·
                refine ⟨7392890896882112530497751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39428751450037933495988005 7392890896882112530497751)
                ·
                  refine ⟨11089336345323168795746627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7392890896882112530497751 11089336345323168795746627)
                  ·
                    refine ⟨16634004517984753193619941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11089336345323168795746627 16634004517984753193619941)
                    ·
                      refine ⟨3118875847122141223803739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16634004517984753193619941 3118875847122141223803739)
                      ·
                        rfl

theorem cell23_6073989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_6073989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6073989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6073989 prefixEnd_6073989 := by exact prefixLift 6073989
  have htrace : WordTrace (prefixWord ++ tailWord_6073989) baseStart_6073989 baseEnd_6073989 := by
    simpa [prefixWord, tailWord_6073989, baseEnd_6073989] using wordTrace_append hprefix tailTrace_6073989
  have hstable : (prefixWord ++ tailWord_6073989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6073989).length < 2 ^ (prefixWord ++ tailWord_6073989).sum := by decide
  have hdescent : baseEnd_6073989 < baseStart_6073989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6073989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074016 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 2, 4]
def baseStart_6074016 : Nat := 118140960795 + 6074016 * 2 ^ 59
def prefixEnd_6074016 : Nat := 4983230072969 + 3 ^ 40 * 6074016 * 2
def baseEnd_6074016 : Nat := 1039629903699937539388705

theorem tailTrace_6074016 : CollatzResearch.WordTrace tailWord_6074016 prefixEnd_6074016 1039629903699937539388705 := by
  unfold tailWord_6074016
  simp only [CollatzResearch.WordTrace]
  refine ⟨110768781781442433094756951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147691709041923244126342601 110768781781442433094756951)
  ·
    refine ⟨166153172672163649642135427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110768781781442433094756951 166153172672163649642135427)
    ·
      refine ⟨249229759008245474463203141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166153172672163649642135427 249229759008245474463203141)
      ·
        refine ⟨46730579814046026461850589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249229759008245474463203141 46730579814046026461850589)
        ·
          refine ⟨17523967430267259923193971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46730579814046026461850589 17523967430267259923193971)
          ·
            refine ⟨26285951145400889884790957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17523967430267259923193971 26285951145400889884790957)
            ·
              refine ⟨9857231679525333706796609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26285951145400889884790957 9857231679525333706796609)
              ·
                refine ⟨7392923759644000280097457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9857231679525333706796609 7392923759644000280097457)
                ·
                  refine ⟨5544692819733000210073093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7392923759644000280097457 5544692819733000210073093)
                  ·
                    refine ⟨1039629903699937539388705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544692819733000210073093 1039629903699937539388705)
                    ·
                      rfl

theorem cell23_6074016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 2, 4].length) (baseStart_6074016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074016 prefixEnd_6074016 := by exact prefixLift 6074016
  have htrace : WordTrace (prefixWord ++ tailWord_6074016) baseStart_6074016 baseEnd_6074016 := by
    simpa [prefixWord, tailWord_6074016, baseEnd_6074016] using wordTrace_append hprefix tailTrace_6074016
  have hstable : (prefixWord ++ tailWord_6074016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074016).length < 2 ^ (prefixWord ++ tailWord_6074016).sum := by decide
  have hdescent : baseEnd_6074016 < baseStart_6074016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074046 : List Nat := [4, 2, 1, 1, 2, 4, 2, 7]
def baseStart_6074046 : Nat := 118140960795 + 6074046 * 2 ^ 59
def prefixEnd_6074046 : Nat := 4983230072969 + 3 ^ 40 * 6074046 * 2
def baseEnd_6074046 : Nat := 115515004278498055584851

theorem tailTrace_6074046 : CollatzResearch.WordTrace tailWord_6074046 prefixEnd_6074046 115515004278498055584851 := by
  unfold tailWord_6074046
  simp only [CollatzResearch.WordTrace]
  refine ⟨27692332219097022664138249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147692438501850787542070661 27692332219097022664138249)
  ·
    refine ⟨20769249164322766998103687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27692332219097022664138249 20769249164322766998103687)
    ·
      refine ⟨31153873746484150497155531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20769249164322766998103687 31153873746484150497155531)
      ·
        refine ⟨46730810619726225745733297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31153873746484150497155531 46730810619726225745733297)
        ·
          refine ⟨35048107964794669309299973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46730810619726225745733297 35048107964794669309299973)
          ·
            refine ⟨6571520243399000495493745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35048107964794669309299973 6571520243399000495493745)
            ·
              refine ⟨4928640182549250371620309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571520243399000495493745 4928640182549250371620309)
              ·
                refine ⟨115515004278498055584851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4928640182549250371620309 115515004278498055584851)
                ·
                  rfl

theorem cell23_6074046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_6074046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074046 prefixEnd_6074046 := by exact prefixLift 6074046
  have htrace : WordTrace (prefixWord ++ tailWord_6074046) baseStart_6074046 baseEnd_6074046 := by
    simpa [prefixWord, tailWord_6074046, baseEnd_6074046] using wordTrace_append hprefix tailTrace_6074046
  have hstable : (prefixWord ++ tailWord_6074046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074046).length < 2 ^ (prefixWord ++ tailWord_6074046).sum := by decide
  have hdescent : baseEnd_6074046 < baseStart_6074046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074096 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 6, 2, 2]
def baseStart_6074096 : Nat := 118140960795 + 6074096 * 2 ^ 59
def prefixEnd_6074096 : Nat := 4983230072969 + 3 ^ 40 * 6074096 * 2
def baseEnd_6074096 : Nat := 3118930789552172305165747

theorem tailTrace_6074096 : CollatzResearch.WordTrace tailWord_6074096 prefixEnd_6074096 3118930789552172305165747 := by
  unfold tailWord_6074096
  simp only [CollatzResearch.WordTrace]
  refine ⟨110770240701297519926213071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147693654268396693234950761 110770240701297519926213071)
  ·
    refine ⟨166155361051946279889319607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110770240701297519926213071 166155361051946279889319607)
    ·
      refine ⟨249233041577919419833979411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166155361051946279889319607 249233041577919419833979411)
      ·
        refine ⟨373849562366879129750969117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249233041577919419833979411 373849562366879129750969117)
        ·
          refine ⟨140193585887579673656613419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 373849562366879129750969117 140193585887579673656613419)
          ·
            refine ⟨210290378831369510484920129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140193585887579673656613419 210290378831369510484920129)
            ·
              refine ⟨157717784123527132863690097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210290378831369510484920129 157717784123527132863690097)
              ·
                refine ⟨118288338092645349647767573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157717784123527132863690097 118288338092645349647767573)
                ·
                  refine ⟨5544765848092750764739105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118288338092645349647767573 5544765848092750764739105)
                  ·
                    refine ⟨4158574386069563073554329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5544765848092750764739105 4158574386069563073554329)
                    ·
                      refine ⟨3118930789552172305165747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158574386069563073554329 3118930789552172305165747)
                      ·
                        rfl

theorem cell23_6074096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 6, 2, 2].length) (baseStart_6074096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074096 prefixEnd_6074096 := by exact prefixLift 6074096
  have htrace : WordTrace (prefixWord ++ tailWord_6074096) baseStart_6074096 baseEnd_6074096 := by
    simpa [prefixWord, tailWord_6074096, baseEnd_6074096] using wordTrace_append hprefix tailTrace_6074096
  have hstable : (prefixWord ++ tailWord_6074096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074096).length < 2 ^ (prefixWord ++ tailWord_6074096).sum := by decide
  have hdescent : baseEnd_6074096 < baseStart_6074096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074125 : List Nat := [1, 7, 2, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6074125 : Nat := 118140960795 + 6074125 * 2 ^ 59
def prefixEnd_6074125 : Nat := 4983230072969 + 3 ^ 40 * 6074125 * 2
def baseEnd_6074125 : Nat := 3118945680491152691703115

theorem tailTrace_6074125 : CollatzResearch.WordTrace tailWord_6074125 prefixEnd_6074125 3118945680491152691703115 := by
  unfold tailWord_6074125
  simp only [CollatzResearch.WordTrace]
  refine ⟨221541539119489977805231829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147694359412993318536821219 221541539119489977805231829)
  ·
    refine ⟨5192379823113046354810121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 221541539119489977805231829 5192379823113046354810121)
    ·
      refine ⟨3894284867334784766107591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5192379823113046354810121 3894284867334784766107591)
      ·
        refine ⟨5841427301002177149161387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894284867334784766107591 5841427301002177149161387)
        ·
          refine ⟨8762140951503265723742081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841427301002177149161387 8762140951503265723742081)
          ·
            refine ⟨6571605713627449292806561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8762140951503265723742081 6571605713627449292806561)
            ·
              refine ⟨4928704285220586969604921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571605713627449292806561 4928704285220586969604921)
              ·
                refine ⟨3696528213915440227203691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928704285220586969604921 3696528213915440227203691)
                ·
                  refine ⟨5544792320873160340805537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696528213915440227203691 5544792320873160340805537)
                  ·
                    refine ⟨4158594240654870255604153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5544792320873160340805537 4158594240654870255604153)
                    ·
                      refine ⟨3118945680491152691703115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158594240654870255604153 3118945680491152691703115)
                      ·
                        rfl

theorem cell23_6074125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6074125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074125 prefixEnd_6074125 := by exact prefixLift 6074125
  have htrace : WordTrace (prefixWord ++ tailWord_6074125) baseStart_6074125 baseEnd_6074125 := by
    simpa [prefixWord, tailWord_6074125, baseEnd_6074125] using wordTrace_append hprefix tailTrace_6074125
  have hstable : (prefixWord ++ tailWord_6074125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074125).length < 2 ^ (prefixWord ++ tailWord_6074125).sum := by decide
  have hdescent : baseEnd_6074125 < baseStart_6074125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074129 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_6074129 : Nat := 118140960795 + 6074129 * 2 ^ 59
def prefixEnd_6074129 : Nat := 4983230072969 + 3 ^ 40 * 6074129 * 2
def baseEnd_6074129 : Nat := 3118947734413770676053095

theorem tailTrace_6074129 : CollatzResearch.WordTrace tailWord_6074129 prefixEnd_6074129 3118947734413770676053095 := by
  unfold tailWord_6074129
  simp only [CollatzResearch.WordTrace]
  refine ⟨221541685011475486488377441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147694456674316990992251627 221541685011475486488377441)
  ·
    refine ⟨166156263758606614866283081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221541685011475486488377441 166156263758606614866283081)
    ·
      refine ⟨124617197818954961149712311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166156263758606614866283081 124617197818954961149712311)
      ·
        refine ⟨186925796728432441724568467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124617197818954961149712311 186925796728432441724568467)
        ·
          refine ⟨280388695092648662586852701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186925796728432441724568467 280388695092648662586852701)
          ·
            refine ⟨105145760659743248470069763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280388695092648662586852701 105145760659743248470069763)
            ·
              refine ⟨157718640989614872705104645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105145760659743248470069763 157718640989614872705104645)
              ·
                refine ⟨29572245185552788632207121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 157718640989614872705104645 29572245185552788632207121)
                ·
                  refine ⟨22179183889164591474155341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29572245185552788632207121 22179183889164591474155341)
                  ·
                    refine ⟨8317193958436721802808253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22179183889164591474155341 8317193958436721802808253)
                    ·
                      refine ⟨3118947734413770676053095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8317193958436721802808253 3118947734413770676053095)
                      ·
                        rfl

theorem cell23_6074129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_6074129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074129 prefixEnd_6074129 := by exact prefixLift 6074129
  have htrace : WordTrace (prefixWord ++ tailWord_6074129) baseStart_6074129 baseEnd_6074129 := by
    simpa [prefixWord, tailWord_6074129, baseEnd_6074129] using wordTrace_append hprefix tailTrace_6074129
  have hstable : (prefixWord ++ tailWord_6074129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074129).length < 2 ^ (prefixWord ++ tailWord_6074129).sum := by decide
  have hdescent : baseEnd_6074129 < baseStart_6074129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074146 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_6074146 : Nat := 118140960795 + 6074146 * 2 ^ 59
def prefixEnd_6074146 : Nat := 4983230072969 + 3 ^ 40 * 6074146 * 2
def baseEnd_6074146 : Nat := 3118956463584897109540517

theorem tailTrace_6074146 : CollatzResearch.WordTrace tailWord_6074146 prefixEnd_6074146 3118956463584897109540517 := by
  unfold tailWord_6074146
  simp only [CollatzResearch.WordTrace]
  refine ⟨55385576263103474597936573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147694870034942598927830861 55385576263103474597936573)
  ·
    refine ⟨20769591098663802974226215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55385576263103474597936573 20769591098663802974226215)
    ·
      refine ⟨31154386647995704461339323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20769591098663802974226215 31154386647995704461339323)
      ·
        refine ⟨46731579971993556692008985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31154386647995704461339323 46731579971993556692008985)
        ·
          refine ⟨35048684978995167519006739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46731579971993556692008985 35048684978995167519006739)
          ·
            refine ⟨52573027468492751278510109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35048684978995167519006739 52573027468492751278510109)
            ·
              refine ⟨19714885300684781729441291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52573027468492751278510109 19714885300684781729441291)
              ·
                refine ⟨29572327951027172594161937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19714885300684781729441291 29572327951027172594161937)
                ·
                  refine ⟨22179245963270379445621453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29572327951027172594161937 22179245963270379445621453)
                  ·
                    refine ⟨8317217236226392292108045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22179245963270379445621453 8317217236226392292108045)
                    ·
                      refine ⟨3118956463584897109540517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8317217236226392292108045 3118956463584897109540517)
                      ·
                        rfl

theorem cell23_6074146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_6074146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074146 prefixEnd_6074146 := by exact prefixLift 6074146
  have htrace : WordTrace (prefixWord ++ tailWord_6074146) baseStart_6074146 baseEnd_6074146 := by
    simpa [prefixWord, tailWord_6074146, baseEnd_6074146] using wordTrace_append hprefix tailTrace_6074146
  have hstable : (prefixWord ++ tailWord_6074146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074146).length < 2 ^ (prefixWord ++ tailWord_6074146).sum := by decide
  have hdescent : baseEnd_6074146 < baseStart_6074146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074186 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_6074186 : Nat := 118140960795 + 6074186 * 2 ^ 59
def prefixEnd_6074186 : Nat := 4983230072969 + 3 ^ 40 * 6074186 * 2
def baseEnd_6074186 : Nat := 3118977002811076953040333

theorem tailTrace_6074186 : CollatzResearch.WordTrace tailWord_6074186 prefixEnd_6074186 3118977002811076953040333 := by
  unfold tailWord_6074186
  simp only [CollatzResearch.WordTrace]
  refine ⟨55385940993067246305800603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147695842648179323482134941 55385940993067246305800603)
  ·
    refine ⟨83078911489600869458700905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55385940993067246305800603 83078911489600869458700905)
    ·
      refine ⟨62309183617200652094025679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83078911489600869458700905 62309183617200652094025679)
      ·
        refine ⟨93463775425800978141038519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62309183617200652094025679 93463775425800978141038519)
        ·
          refine ⟨140195663138701467211557779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93463775425800978141038519 140195663138701467211557779)
          ·
            refine ⟨210293494708052200817336669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140195663138701467211557779 210293494708052200817336669)
            ·
              refine ⟨78860060515519575306501251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210293494708052200817336669 78860060515519575306501251)
              ·
                refine ⟨118290090773279362959751877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78860060515519575306501251 118290090773279362959751877)
                ·
                  refine ⟨22179392019989880554953477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118290090773279362959751877 22179392019989880554953477)
                  ·
                    refine ⟨4158636003748102604053777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22179392019989880554953477 4158636003748102604053777)
                    ·
                      refine ⟨3118977002811076953040333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4158636003748102604053777 3118977002811076953040333)
                      ·
                        rfl

theorem cell23_6074186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_6074186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074186 prefixEnd_6074186 := by exact prefixLift 6074186
  have htrace : WordTrace (prefixWord ++ tailWord_6074186) baseStart_6074186 baseEnd_6074186 := by
    simpa [prefixWord, tailWord_6074186, baseEnd_6074186] using wordTrace_append hprefix tailTrace_6074186
  have hstable : (prefixWord ++ tailWord_6074186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074186).length < 2 ^ (prefixWord ++ tailWord_6074186).sum := by decide
  have hdescent : baseEnd_6074186 < baseStart_6074186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074219 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 3]
def baseStart_6074219 : Nat := 118140960795 + 6074219 * 2 ^ 59
def prefixEnd_6074219 : Nat := 4983230072969 + 3 ^ 40 * 6074219 * 2
def baseEnd_6074219 : Nat := 3118993947672675323927681

theorem tailTrace_6074219 : CollatzResearch.WordTrace tailWord_6074219 prefixEnd_6074219 3118993947672675323927681 := by
  unfold tailWord_6074219
  simp only [CollatzResearch.WordTrace]
  refine ⟨221544967581149431859153711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147696645054099621239435807 221544967581149431859153711)
  ·
    refine ⟨332317451371724147788730567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221544967581149431859153711 332317451371724147788730567)
    ·
      refine ⟨498476177057586221683095851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332317451371724147788730567 498476177057586221683095851)
      ·
        refine ⟨747714265586379332524643777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 498476177057586221683095851 747714265586379332524643777)
        ·
          refine ⟨560785699189784499393482833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747714265586379332524643777 560785699189784499393482833)
          ·
            refine ⟨420589274392338374545112125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560785699189784499393482833 420589274392338374545112125)
            ·
              refine ⟨157720977897126890454417047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420589274392338374545112125 157720977897126890454417047)
              ·
                refine ⟨236581466845690335681625571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157720977897126890454417047 236581466845690335681625571)
                ·
                  refine ⟨354872200268535503522438357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236581466845690335681625571 354872200268535503522438357)
                  ·
                    refine ⟨8317317193793800863807149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 354872200268535503522438357 8317317193793800863807149)
                    ·
                      refine ⟨3118993947672675323927681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8317317193793800863807149 3118993947672675323927681)
                      ·
                        rfl

theorem cell23_6074219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 3].length) (baseStart_6074219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074219 prefixEnd_6074219 := by exact prefixLift 6074219
  have htrace : WordTrace (prefixWord ++ tailWord_6074219) baseStart_6074219 baseEnd_6074219 := by
    simpa [prefixWord, tailWord_6074219, baseEnd_6074219] using wordTrace_append hprefix tailTrace_6074219
  have hstable : (prefixWord ++ tailWord_6074219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074219).length < 2 ^ (prefixWord ++ tailWord_6074219).sum := by decide
  have hdescent : baseEnd_6074219 < baseStart_6074219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074239 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 5, 5]
def baseStart_6074239 : Nat := 118140960795 + 6074239 * 2 ^ 59
def prefixEnd_6074239 : Nat := 4983230072969 + 3 ^ 40 * 6074239 * 2
def baseEnd_6074239 : Nat := 1039668072428588415225863

theorem tailTrace_6074239 : CollatzResearch.WordTrace tailWord_6074239 prefixEnd_6074239 1039668072428588415225863 := by
  unfold tailWord_6074239
  simp only [CollatzResearch.WordTrace]
  refine ⟨221545697041076975274881771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147697131360717983516587847 221545697041076975274881771)
  ·
    refine ⟨332318545561615462912322657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221545697041076975274881771 332318545561615462912322657)
    ·
      refine ⟨249238909171211597184241993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332318545561615462912322657 249238909171211597184241993)
      ·
        refine ⟨186929181878408697888181495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249238909171211597184241993 186929181878408697888181495)
        ·
          refine ⟨280393772817613046832272243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186929181878408697888181495 280393772817613046832272243)
          ·
            refine ⟨420590659226419570248408365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280393772817613046832272243 420590659226419570248408365)
            ·
              refine ⟨157721497209907338843153137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420590659226419570248408365 157721497209907338843153137)
              ·
                refine ⟨118291122907430504132364853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 157721497209907338843153137 118291122907430504132364853)
                ·
                  refine ⟨11089792772571609762409205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118291122907430504132364853 11089792772571609762409205)
                  ·
                    refine ⟨1039668072428588415225863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11089792772571609762409205 1039668072428588415225863)
                    ·
                      rfl

theorem cell23_6074239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_6074239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074239 prefixEnd_6074239 := by exact prefixLift 6074239
  have htrace : WordTrace (prefixWord ++ tailWord_6074239) baseStart_6074239 baseEnd_6074239 := by
    simpa [prefixWord, tailWord_6074239, baseEnd_6074239] using wordTrace_append hprefix tailTrace_6074239
  have hstable : (prefixWord ++ tailWord_6074239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074239).length < 2 ^ (prefixWord ++ tailWord_6074239).sum := by decide
  have hdescent : baseEnd_6074239 < baseStart_6074239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074247 : List Nat := [1, 1, 4, 2, 4, 1, 3, 2, 1, 4]
def baseStart_6074247 : Nat := 118140960795 + 6074247 * 2 ^ 59
def prefixEnd_6074247 : Nat := 4983230072969 + 3 ^ 40 * 6074247 * 2
def baseEnd_6074247 : Nat := 1039669441710333738125851

theorem tailTrace_6074247 : CollatzResearch.WordTrace tailWord_6074247 prefixEnd_6074247 1039669441710333738125851 := by
  unfold tailWord_6074247
  simp only [CollatzResearch.WordTrace]
  refine ⟨221545988825047992641172995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147697325883365328427448663 221545988825047992641172995)
  ·
    refine ⟨332318983237571988961759493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221545988825047992641172995 332318983237571988961759493)
    ·
      refine ⟨62309809357044747930329905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 332318983237571988961759493 62309809357044747930329905)
      ·
        refine ⟨46732357017783560947747429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62309809357044747930329905 46732357017783560947747429)
        ·
          refine ⟨8762316940834417677702643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46732357017783560947747429 8762316940834417677702643)
          ·
            refine ⟨13143475411251626516553965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762316940834417677702643 13143475411251626516553965)
            ·
              refine ⟨4928803279219359943707737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13143475411251626516553965 4928803279219359943707737)
              ·
                refine ⟨3696602459414519957780803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4928803279219359943707737 3696602459414519957780803)
                ·
                  refine ⟨5544903689121779936671205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3696602459414519957780803 5544903689121779936671205)
                  ·
                    refine ⟨1039669441710333738125851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544903689121779936671205 1039669441710333738125851)
                    ·
                      rfl

theorem cell23_6074247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_6074247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074247 prefixEnd_6074247 := by exact prefixLift 6074247
  have htrace : WordTrace (prefixWord ++ tailWord_6074247) baseStart_6074247 baseEnd_6074247 := by
    simpa [prefixWord, tailWord_6074247, baseEnd_6074247] using wordTrace_append hprefix tailTrace_6074247
  have hstable : (prefixWord ++ tailWord_6074247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074247).length < 2 ^ (prefixWord ++ tailWord_6074247).sum := by decide
  have hdescent : baseEnd_6074247 < baseStart_6074247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074260 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 6]
def baseStart_6074260 : Nat := 118140960795 + 6074260 * 2 ^ 59
def prefixEnd_6074260 : Nat := 4983230072969 + 3 ^ 40 * 6074260 * 2
def baseEnd_6074260 : Nat := 346557222264389962612777

theorem tailTrace_6074260 : CollatzResearch.WordTrace tailWord_6074260 prefixEnd_6074260 346557222264389962612777 := by
  unfold tailWord_6074260
  simp only [CollatzResearch.WordTrace]
  refine ⟨110773231487000447930698117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147697641982667263907597489 110773231487000447930698117)
  ·
    refine ⟨20769980903812583987005897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110773231487000447930698117 20769980903812583987005897)
    ·
      refine ⟨15577485677859437990254423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20769980903812583987005897 15577485677859437990254423)
      ·
        refine ⟨23366228516789156985381635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15577485677859437990254423 23366228516789156985381635)
        ·
          refine ⟨35049342775183735478072453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23366228516789156985381635 35049342775183735478072453)
          ·
            refine ⟨6571751770346950402138585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35049342775183735478072453 6571751770346950402138585)
            ·
              refine ⟨4928813827760212801603939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6571751770346950402138585 4928813827760212801603939)
              ·
                refine ⟨7393220741640319202405909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4928813827760212801603939 7393220741640319202405909)
                ·
                  refine ⟨346557222264389962612777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7393220741640319202405909 346557222264389962612777)
                  ·
                    rfl

theorem cell23_6074260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_6074260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074260 prefixEnd_6074260 := by exact prefixLift 6074260
  have htrace : WordTrace (prefixWord ++ tailWord_6074260) baseStart_6074260 baseEnd_6074260 := by
    simpa [prefixWord, tailWord_6074260, baseEnd_6074260] using wordTrace_append hprefix tailTrace_6074260
  have hstable : (prefixWord ++ tailWord_6074260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074260).length < 2 ^ (prefixWord ++ tailWord_6074260).sum := by decide
  have hdescent : baseEnd_6074260 < baseStart_6074260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074273 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 3, 5]
def baseStart_6074273 : Nat := 118140960795 + 6074273 * 2 ^ 59
def prefixEnd_6074273 : Nat := 4983230072969 + 3 ^ 40 * 6074273 * 2
def baseEnd_6074273 : Nat := 1039673891876006037550811

theorem tailTrace_6074273 : CollatzResearch.WordTrace tailWord_6074273 prefixEnd_6074273 1039673891876006037550811 := by
  unfold tailWord_6074273
  simp only [CollatzResearch.WordTrace]
  refine ⟨221546937122953799081619473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147697958081969199387746315 221546937122953799081619473)
  ·
    refine ⟨166160202842215349311214605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221546937122953799081619473 166160202842215349311214605)
    ·
      refine ⟨62310076065830755991705477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166160202842215349311214605 62310076065830755991705477)
      ·
        refine ⟨11683139262343266748444777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62310076065830755991705477 11683139262343266748444777)
        ·
          refine ⟨8762354446757450061333583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11683139262343266748444777 8762354446757450061333583)
          ·
            refine ⟨13143531670136175092000375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762354446757450061333583 13143531670136175092000375)
            ·
              refine ⟨19715297505204262638000563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13143531670136175092000375 19715297505204262638000563)
              ·
                refine ⟨29572946257806393957000845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19715297505204262638000563 29572946257806393957000845)
                ·
                  refine ⟨11089854846677397733875317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29572946257806393957000845 11089854846677397733875317)
                  ·
                    refine ⟨1039673891876006037550811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11089854846677397733875317 1039673891876006037550811)
                    ·
                      rfl

theorem cell23_6074273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_6074273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074273 prefixEnd_6074273 := by exact prefixLift 6074273
  have htrace : WordTrace (prefixWord ++ tailWord_6074273) baseStart_6074273 baseEnd_6074273 := by
    simpa [prefixWord, tailWord_6074273, baseEnd_6074273] using wordTrace_append hprefix tailTrace_6074273
  have hstable : (prefixWord ++ tailWord_6074273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074273).length < 2 ^ (prefixWord ++ tailWord_6074273).sum := by decide
  have hdescent : baseEnd_6074273 < baseStart_6074273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074303 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 2, 4]
def baseStart_6074303 : Nat := 118140960795 + 6074303 * 2 ^ 59
def prefixEnd_6074303 : Nat := 4983230072969 + 3 ^ 40 * 6074303 * 2
def baseEnd_6074303 : Nat := 1039679026682550998425765

theorem tailTrace_6074303 : CollatzResearch.WordTrace tailWord_6074303 prefixEnd_6074303 1039679026682550998425765 := by
  unfold tailWord_6074303
  simp only [CollatzResearch.WordTrace]
  refine ⟨221548031312845114205211563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147698687541896742803474375 221548031312845114205211563)
  ·
    refine ⟨332322046969267671307817345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221548031312845114205211563 332322046969267671307817345)
    ·
      refine ⟨249241535226950753480863009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332322046969267671307817345 249241535226950753480863009)
      ·
        refine ⟨186931151420213065110647257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249241535226950753480863009 186931151420213065110647257)
        ·
          refine ⟨140198363565159798832985443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186931151420213065110647257 140198363565159798832985443)
          ·
            refine ⟨210297545347739698249478165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140198363565159798832985443 210297545347739698249478165)
            ·
              refine ⟨9857697438175298355444289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 210297545347739698249478165 9857697438175298355444289)
              ·
                refine ⟨7393273078631473766583217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9857697438175298355444289 7393273078631473766583217)
                ·
                  refine ⟨5544954808973605324937413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7393273078631473766583217 5544954808973605324937413)
                  ·
                    refine ⟨1039679026682550998425765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5544954808973605324937413 1039679026682550998425765)
                    ·
                      rfl

theorem cell23_6074303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 4].length) (baseStart_6074303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074303 prefixEnd_6074303 := by exact prefixLift 6074303
  have htrace : WordTrace (prefixWord ++ tailWord_6074303) baseStart_6074303 baseEnd_6074303 := by
    simpa [prefixWord, tailWord_6074303, baseEnd_6074303] using wordTrace_append hprefix tailTrace_6074303
  have hstable : (prefixWord ++ tailWord_6074303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074303).length < 2 ^ (prefixWord ++ tailWord_6074303).sum := by decide
  have hdescent : baseEnd_6074303 < baseStart_6074303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074309 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_6074309 : Nat := 118140960795 + 6074309 * 2 ^ 59
def prefixEnd_6074309 : Nat := 4983230072969 + 3 ^ 40 * 6074309 * 2
def baseEnd_6074309 : Nat := 3119040160931579971802267

theorem tailTrace_6074309 : CollatzResearch.WordTrace tailWord_6074309 prefixEnd_6074309 3119040160931579971802267 := by
  unfold tailWord_6074309
  simp only [CollatzResearch.WordTrace]
  refine ⟨221548250150823377229929981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147698833433882251486619987 221548250150823377229929981)
  ·
    refine ⟨83080593806558766461223743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221548250150823377229929981 83080593806558766461223743)
    ·
      refine ⟨124620890709838149691835615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83080593806558766461223743 124620890709838149691835615)
      ·
        refine ⟨186931336064757224537753423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124620890709838149691835615 186931336064757224537753423)
        ·
          refine ⟨280397004097135836806630135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186931336064757224537753423 280397004097135836806630135)
          ·
            refine ⟨420595506145703755209945203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280397004097135836806630135 420595506145703755209945203)
            ·
              refine ⟨630893259218555632814917805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420595506145703755209945203 630893259218555632814917805)
              ·
                refine ⟨236584972206958362305594177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630893259218555632814917805 236584972206958362305594177)
                ·
                  refine ⟨177438729155218771729195633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236584972206958362305594177 177438729155218771729195633)
                  ·
                    refine ⟨133079046866414078796896725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177438729155218771729195633 133079046866414078796896725)
                    ·
                      refine ⟨3119040160931579971802267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133079046866414078796896725 3119040160931579971802267)
                      ·
                        rfl

theorem cell23_6074309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_6074309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074309 prefixEnd_6074309 := by exact prefixLift 6074309
  have htrace : WordTrace (prefixWord ++ tailWord_6074309) baseStart_6074309 baseEnd_6074309 := by
    simpa [prefixWord, tailWord_6074309, baseEnd_6074309] using wordTrace_append hprefix tailTrace_6074309
  have hstable : (prefixWord ++ tailWord_6074309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074309).length < 2 ^ (prefixWord ++ tailWord_6074309).sum := by decide
  have hdescent : baseEnd_6074309 < baseStart_6074309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074316 : List Nat := [2, 2, 1, 4, 1, 2, 3, 8]
def baseStart_6074316 : Nat := 118140960795 + 6074316 * 2 ^ 59
def prefixEnd_6074316 : Nat := 4983230072969 + 3 ^ 40 * 6074316 * 2
def baseEnd_6074316 : Nat := 115520139085043016459805

theorem tailTrace_6074316 : CollatzResearch.WordTrace tailWord_6074316 prefixEnd_6074316 115520139085043016459805 := by
  unfold tailWord_6074316
  simp only [CollatzResearch.WordTrace]
  refine ⟨110774252730899008712717401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147699003641198678283623201 110774252730899008712717401)
  ·
    refine ⟨83080689548174256534538051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110774252730899008712717401 83080689548174256534538051)
    ·
      refine ⟨124621034322261384801807077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83080689548174256534538051 124621034322261384801807077)
      ·
        refine ⟨23366443935424009650338827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124621034322261384801807077 23366443935424009650338827)
        ·
          refine ⟨35049665903136014475508241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23366443935424009650338827 35049665903136014475508241)
          ·
            refine ⟨26287249427352010856631181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35049665903136014475508241 26287249427352010856631181)
            ·
              refine ⟨9857718535257004071236693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26287249427352010856631181 9857718535257004071236693)
              ·
                refine ⟨115520139085043016459805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9857718535257004071236693 115520139085043016459805)
                ·
                  rfl

theorem cell23_6074316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 8].length) (baseStart_6074316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074316 prefixEnd_6074316 := by exact prefixLift 6074316
  have htrace : WordTrace (prefixWord ++ tailWord_6074316) baseStart_6074316 baseEnd_6074316 := by
    simpa [prefixWord, tailWord_6074316, baseEnd_6074316] using wordTrace_append hprefix tailTrace_6074316
  have hstable : (prefixWord ++ tailWord_6074316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074316).length < 2 ^ (prefixWord ++ tailWord_6074316).sum := by decide
  have hdescent : baseEnd_6074316 < baseStart_6074316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074360 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_6074360 : Nat := 118140960795 + 6074360 * 2 ^ 59
def prefixEnd_6074360 : Nat := 4983230072969 + 3 ^ 40 * 6074360 * 2
def baseEnd_6074360 : Nat := 3119066348444959272264533

theorem tailTrace_6074360 : CollatzResearch.WordTrace tailWord_6074360 prefixEnd_6074360 3119066348444959272264533 := by
  unfold tailWord_6074360
  simp only [CollatzResearch.WordTrace]
  refine ⟨110775055136819306470018267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147700073515759075293357689 110775055136819306470018267)
  ·
    refine ⟨166162582705228959705027401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110775055136819306470018267 166162582705228959705027401)
    ·
      refine ⟨124621937028921719778770551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166162582705228959705027401 124621937028921719778770551)
      ·
        refine ⟨186932905543382579668155827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124621937028921719778770551 186932905543382579668155827)
        ·
          refine ⟨280399358315073869502233741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186932905543382579668155827 280399358315073869502233741)
          ·
            refine ⟨105149759368152701063337653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280399358315073869502233741 105149759368152701063337653)
            ·
              refine ⟨9857789940764315724687905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105149759368152701063337653 9857789940764315724687905)
              ·
                refine ⟨7393342455573236793515929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9857789940764315724687905 7393342455573236793515929)
                ·
                  refine ⟨5545006841679927595136947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7393342455573236793515929 5545006841679927595136947)
                  ·
                    refine ⟨8317510262519891392705421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5545006841679927595136947 8317510262519891392705421)
                    ·
                      refine ⟨3119066348444959272264533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8317510262519891392705421 3119066348444959272264533)
                      ·
                        rfl

theorem cell23_6074360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_6074360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074360 prefixEnd_6074360 := by exact prefixLift 6074360
  have htrace : WordTrace (prefixWord ++ tailWord_6074360) baseStart_6074360 baseEnd_6074360 := by
    simpa [prefixWord, tailWord_6074360, baseEnd_6074360] using wordTrace_append hprefix tailTrace_6074360
  have hstable : (prefixWord ++ tailWord_6074360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074360).length < 2 ^ (prefixWord ++ tailWord_6074360).sum := by decide
  have hdescent : baseEnd_6074360 < baseStart_6074360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6074374 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6074374 : Nat := 118140960795 + 6074374 * 2 ^ 59
def prefixEnd_6074374 : Nat := 4983230072969 + 3 ^ 40 * 6074374 * 2
def baseEnd_6074374 : Nat := 3119073537174122217489469

theorem tailTrace_6074374 : CollatzResearch.WordTrace tailWord_6074374 prefixEnd_6074374 3119073537174122217489469 := by
  unfold tailWord_6074374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923456902987121666595193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 147700413930391928887364117 6923456902987121666595193)
  ·
    refine ⟨5192592677240341249946395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6923456902987121666595193 5192592677240341249946395)
    ·
      refine ⟨7788889015860511874919593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192592677240341249946395 7788889015860511874919593)
      ·
        refine ⟨5841666761895383906189695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7788889015860511874919593 5841666761895383906189695)
        ·
          refine ⟨8762500142843075859284543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841666761895383906189695 8762500142843075859284543)
          ·
            refine ⟨13143750214264613788926815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8762500142843075859284543 13143750214264613788926815)
            ·
              refine ⟨19715625321396920683390223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13143750214264613788926815 19715625321396920683390223)
              ·
                refine ⟨29573437982095381025085335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19715625321396920683390223 29573437982095381025085335)
                ·
                  refine ⟨44360156973143071537628003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29573437982095381025085335 44360156973143071537628003)
                  ·
                    refine ⟨66540235459714607306442005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44360156973143071537628003 66540235459714607306442005)
                    ·
                      refine ⟨3119073537174122217489469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66540235459714607306442005 3119073537174122217489469)
                      ·
                        rfl

theorem cell23_6074374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6074374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6074374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6074374 prefixEnd_6074374 := by exact prefixLift 6074374
  have htrace : WordTrace (prefixWord ++ tailWord_6074374) baseStart_6074374 baseEnd_6074374 := by
    simpa [prefixWord, tailWord_6074374, baseEnd_6074374] using wordTrace_append hprefix tailTrace_6074374
  have hstable : (prefixWord ++ tailWord_6074374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6074374).length < 2 ^ (prefixWord ++ tailWord_6074374).sum := by decide
  have hdescent : baseEnd_6074374 < baseStart_6074374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6074374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
