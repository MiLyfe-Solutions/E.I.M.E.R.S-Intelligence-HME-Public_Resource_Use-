import V185TrunkScan23Chunk0925

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5480871 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5480871 : Nat := 118140960795 + 5480871 * 2 ^ 59
def prefixEnd_5480871 : Nat := 4983230072969 + 3 ^ 40 * 5480871 * 2
def baseEnd_5480871 : Nat := 2814321228288730800706439

theorem tailTrace_5480871 : CollatzResearch.WordTrace tailWord_5480871 prefixEnd_5480871 2814321228288730800706439 := by
  unfold tailWord_5480871
  simp only [CollatzResearch.WordTrace]
  refine ⟨199903788126747900088506467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133269192084498600059004311 199903788126747900088506467)
  ·
    refine ⟨299855682190121850132759701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199903788126747900088506467 299855682190121850132759701)
    ·
      refine ⟨14055735102661961724973111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299855682190121850132759701 14055735102661961724973111)
      ·
        refine ⟨21083602653992942587459667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14055735102661961724973111 21083602653992942587459667)
        ·
          refine ⟨31625403980989413881189501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21083602653992942587459667 31625403980989413881189501)
          ·
            refine ⟨11859526492871030205446063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31625403980989413881189501 11859526492871030205446063)
            ·
              refine ⟨17789289739306545308169095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11859526492871030205446063 17789289739306545308169095)
              ·
                refine ⟨26683934608959817962253643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17789289739306545308169095 26683934608959817962253643)
                ·
                  refine ⟨40025901913439726943380465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26683934608959817962253643 40025901913439726943380465)
                  ·
                    refine ⟨30019426435079795207535349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40025901913439726943380465 30019426435079795207535349)
                    ·
                      refine ⟨2814321228288730800706439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30019426435079795207535349 2814321228288730800706439)
                      ·
                        rfl

theorem cell23_5480871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5480871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480871 prefixEnd_5480871 := by exact prefixLift 5480871
  have htrace : WordTrace (prefixWord ++ tailWord_5480871) baseStart_5480871 baseEnd_5480871 := by
    simpa [prefixWord, tailWord_5480871, baseEnd_5480871] using wordTrace_append hprefix tailTrace_5480871
  have hstable : (prefixWord ++ tailWord_5480871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480871).length < 2 ^ (prefixWord ++ tailWord_5480871).sum := by decide
  have hdescent : baseEnd_5480871 < baseStart_5480871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480921 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 6]
def baseStart_5480921 : Nat := 118140960795 + 5480921 * 2 ^ 59
def prefixEnd_5480921 : Nat := 4983230072969 + 3 ^ 40 * 5480921 * 2
def baseEnd_5480921 : Nat := 312705211369050622786801

theorem tailTrace_5480921 : CollatzResearch.WordTrace tailWord_5480921 prefixEnd_5480921 312705211369050622786801 := by
  unfold tailWord_5480921
  simp only [CollatzResearch.WordTrace]
  refine ⟨199905611776566758627826617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133270407851044505751884411 199905611776566758627826617)
  ·
    refine ⟨149929208832425068970869963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199905611776566758627826617 149929208832425068970869963)
    ·
      refine ⟨224893813248637603456304945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149929208832425068970869963 224893813248637603456304945)
      ·
        refine ⟨168670359936478202592228709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224893813248637603456304945 168670359936478202592228709)
        ·
          refine ⟨31625692488089662986042883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168670359936478202592228709 31625692488089662986042883)
          ·
            refine ⟨47438538732134494479064325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31625692488089662986042883 47438538732134494479064325)
            ·
              refine ⟨8894726012275217714824561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47438538732134494479064325 8894726012275217714824561)
              ·
                refine ⟨6671044509206413286118421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8894726012275217714824561 6671044509206413286118421)
                ·
                  refine ⟨312705211369050622786801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6671044509206413286118421 312705211369050622786801)
                  ·
                    rfl

theorem cell23_5480921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 6].length) (baseStart_5480921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480921 prefixEnd_5480921 := by exact prefixLift 5480921
  have htrace : WordTrace (prefixWord ++ tailWord_5480921) baseStart_5480921 baseEnd_5480921 := by
    simpa [prefixWord, tailWord_5480921, baseEnd_5480921] using wordTrace_append hprefix tailTrace_5480921
  have hstable : (prefixWord ++ tailWord_5480921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480921).length < 2 ^ (prefixWord ++ tailWord_5480921).sum := by decide
  have hdescent : baseEnd_5480921 < baseStart_5480921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480925 : List Nat := [1, 4, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_5480925 : Nat := 118140960795 + 5480925 * 2 ^ 59
def prefixEnd_5480925 : Nat := 4983230072969 + 3 ^ 40 * 5480925 * 2
def baseEnd_5480925 : Nat := 938116318748024529810397

theorem tailTrace_5480925 : CollatzResearch.WordTrace tailWord_5480925 prefixEnd_5480925 938116318748024529810397 := by
  unfold tailWord_5480925
  simp only [CollatzResearch.WordTrace]
  refine ⟨199905757668552267310972229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133270505112368178207314819 199905757668552267310972229)
  ·
    refine ⟨37482329562853550120807293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199905757668552267310972229 37482329562853550120807293)
    ·
      refine ⟨14055873586070081295302735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37482329562853550120807293 14055873586070081295302735)
      ·
        refine ⟨21083810379105121942954103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14055873586070081295302735 21083810379105121942954103)
        ·
          refine ⟨31625715568657682914431155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21083810379105121942954103 31625715568657682914431155)
          ·
            refine ⟨47438573352986524371646733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31625715568657682914431155 47438573352986524371646733)
            ·
              refine ⟨17789465007369946639367525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47438573352986524371646733 17789465007369946639367525)
              ·
                refine ⟨3335524688881864994881411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17789465007369946639367525 3335524688881864994881411)
                ·
                  refine ⟨5003287033322797492322117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335524688881864994881411 5003287033322797492322117)
                  ·
                    refine ⟨938116318748024529810397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003287033322797492322117 938116318748024529810397)
                    ·
                      rfl

theorem cell23_5480925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_5480925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480925 prefixEnd_5480925 := by exact prefixLift 5480925
  have htrace : WordTrace (prefixWord ++ tailWord_5480925) baseStart_5480925 baseEnd_5480925 := by
    simpa [prefixWord, tailWord_5480925, baseEnd_5480925] using wordTrace_append hprefix tailTrace_5480925
  have hstable : (prefixWord ++ tailWord_5480925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480925).length < 2 ^ (prefixWord ++ tailWord_5480925).sum := by decide
  have hdescent : baseEnd_5480925 < baseStart_5480925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480944 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_5480944 : Nat := 118140960795 + 5480944 * 2 ^ 59
def prefixEnd_5480944 : Nat := 4983230072969 + 3 ^ 40 * 5480944 * 2
def baseEnd_5480944 : Nat := 2814358712376509015093603

theorem tailTrace_5480944 : CollatzResearch.WordTrace tailWord_5480944 prefixEnd_5480944 2814358712376509015093603 := by
  unfold tailWord_5480944
  simp only [CollatzResearch.WordTrace]
  refine ⟨99953225327741716777956943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133270967103655622370609257 99953225327741716777956943)
  ·
    refine ⟨149929837991612575166935415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99953225327741716777956943 149929837991612575166935415)
    ·
      refine ⟨224894756987418862750403123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149929837991612575166935415 224894756987418862750403123)
      ·
        refine ⟨337342135481128294125604685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224894756987418862750403123 337342135481128294125604685)
        ·
          refine ⟨126503300805423110297101757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337342135481128294125604685 126503300805423110297101757)
          ·
            refine ⟨47438737802033666361413159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126503300805423110297101757 47438737802033666361413159)
            ·
              refine ⟨71158106703050499542119739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47438737802033666361413159 71158106703050499542119739)
              ·
                refine ⟨106737160054575749313179609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71158106703050499542119739 106737160054575749313179609)
                ·
                  refine ⟨80052870040931811984884707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106737160054575749313179609 80052870040931811984884707)
                  ·
                    refine ⟨120079305061397717977327061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80052870040931811984884707 120079305061397717977327061)
                    ·
                      refine ⟨2814358712376509015093603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120079305061397717977327061 2814358712376509015093603)
                      ·
                        rfl

theorem cell23_5480944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_5480944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480944 prefixEnd_5480944 := by exact prefixLift 5480944
  have htrace : WordTrace (prefixWord ++ tailWord_5480944) baseStart_5480944 baseEnd_5480944 := by
    simpa [prefixWord, tailWord_5480944, baseEnd_5480944] using wordTrace_append hprefix tailTrace_5480944
  have hstable : (prefixWord ++ tailWord_5480944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480944).length < 2 ^ (prefixWord ++ tailWord_5480944).sum := by decide
  have hdescent : baseEnd_5480944 < baseStart_5480944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480965 : List Nat := [1, 3, 1, 1, 2, 2, 3, 5, 1, 1, 3]
def baseStart_5480965 : Nat := 118140960795 + 5480965 * 2 ^ 59
def prefixEnd_5480965 : Nat := 4983230072969 + 3 ^ 40 * 5480965 * 2
def baseEnd_5480965 : Nat := 2814369495470253432931007

theorem tailTrace_5480965 : CollatzResearch.WordTrace tailWord_5480965 prefixEnd_5480965 2814369495470253432931007 := by
  unfold tailWord_5480965
  simp only [CollatzResearch.WordTrace]
  refine ⟨199907216588407354142428349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133271477725604902761618899 199907216588407354142428349)
  ·
    refine ⟨74965206220652757803410631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199907216588407354142428349 74965206220652757803410631)
    ·
      refine ⟨112447809330979136705115947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74965206220652757803410631 112447809330979136705115947)
      ·
        refine ⟨168671713996468705057673921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112447809330979136705115947 168671713996468705057673921)
        ·
          refine ⟨126503785497351528793255441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168671713996468705057673921 126503785497351528793255441)
          ·
            refine ⟨94877839123013646594941581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126503785497351528793255441 94877839123013646594941581)
            ·
              refine ⟨35579189671130117473103093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94877839123013646594941581 35579189671130117473103093)
              ·
                refine ⟨3335549031668448513103415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35579189671130117473103093 3335549031668448513103415)
                ·
                  refine ⟨5003323547502672769655123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335549031668448513103415 5003323547502672769655123)
                  ·
                    refine ⟨7504985321254009154482685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5003323547502672769655123 7504985321254009154482685)
                    ·
                      refine ⟨2814369495470253432931007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7504985321254009154482685 2814369495470253432931007)
                      ·
                        rfl

theorem cell23_5480965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_5480965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480965 prefixEnd_5480965 := by exact prefixLift 5480965
  have htrace : WordTrace (prefixWord ++ tailWord_5480965) baseStart_5480965 baseEnd_5480965 := by
    simpa [prefixWord, tailWord_5480965, baseEnd_5480965] using wordTrace_append hprefix tailTrace_5480965
  have hstable : (prefixWord ++ tailWord_5480965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480965).length < 2 ^ (prefixWord ++ tailWord_5480965).sum := by decide
  have hdescent : baseEnd_5480965 < baseStart_5480965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481008 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3]
def baseStart_5481008 : Nat := 118140960795 + 5481008 * 2 ^ 59
def prefixEnd_5481008 : Nat := 4983230072969 + 3 ^ 40 * 5481008 * 2
def baseEnd_5481008 : Nat := 2814391575138396764693309

theorem tailTrace_5481008 : CollatzResearch.WordTrace tailWord_5481008 prefixEnd_5481008 2814391575138396764693309 := by
  unfold tailWord_5481008
  simp only [CollatzResearch.WordTrace]
  refine ⟨99954392463625786243121839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133272523284834381657495785 99954392463625786243121839)
  ·
    refine ⟨149931588695438679364682759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99954392463625786243121839 149931588695438679364682759)
    ·
      refine ⟨224897383043158019047024139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149931588695438679364682759 224897383043158019047024139)
      ·
        refine ⟨337346074564737028570536209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224897383043158019047024139 337346074564737028570536209)
        ·
          refine ⟨253009555923552771427902157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337346074564737028570536209 253009555923552771427902157)
          ·
            refine ⟨94878583471332289285463309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253009555923552771427902157 94878583471332289285463309)
            ·
              refine ⟨35579468801749608482048741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94878583471332289285463309 35579468801749608482048741)
              ·
                refine ⟨6671150400328051590384139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35579468801749608482048741 6671150400328051590384139)
                ·
                  refine ⟨10006725600492077385576209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6671150400328051590384139 10006725600492077385576209)
                  ·
                    refine ⟨7505044200369058039182157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10006725600492077385576209 7505044200369058039182157)
                    ·
                      refine ⟨2814391575138396764693309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7505044200369058039182157 2814391575138396764693309)
                      ·
                        rfl

theorem cell23_5481008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_5481008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481008 prefixEnd_5481008 := by exact prefixLift 5481008
  have htrace : WordTrace (prefixWord ++ tailWord_5481008) baseStart_5481008 baseEnd_5481008 := by
    simpa [prefixWord, tailWord_5481008, baseEnd_5481008] using wordTrace_append hprefix tailTrace_5481008
  have hstable : (prefixWord ++ tailWord_5481008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481008).length < 2 ^ (prefixWord ++ tailWord_5481008).sum := by decide
  have hdescent : baseEnd_5481008 < baseStart_5481008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481025 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_5481025 : Nat := 118140960795 + 5481025 * 2 ^ 59
def prefixEnd_5481025 : Nat := 4983230072969 + 3 ^ 40 * 5481025 * 2
def baseEnd_5481025 : Nat := 2814400304309523198180731

theorem tailTrace_5481025 : CollatzResearch.WordTrace tailWord_5481025 prefixEnd_5481025 2814400304309523198180731 := by
  unfold tailWord_5481025
  simp only [CollatzResearch.WordTrace]
  refine ⟨199909404968189984389612529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133272936645459989593075019 199909404968189984389612529)
  ·
    refine ⟨149932053726142488292209397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199909404968189984389612529 149932053726142488292209397)
    ·
      refine ⟨14056130036825858277394631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149932053726142488292209397 14056130036825858277394631)
      ·
        refine ⟨21084195055238787416091947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14056130036825858277394631 21084195055238787416091947)
        ·
          refine ⟨31626292582858181124137921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21084195055238787416091947 31626292582858181124137921)
          ·
            refine ⟨23719719437143635843103441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31626292582858181124137921 23719719437143635843103441)
            ·
              refine ⟨17789789577857726882327581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23719719437143635843103441 17789789577857726882327581)
              ·
                refine ⟨6671171091696647580872843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17789789577857726882327581 6671171091696647580872843)
                ·
                  refine ⟨10006756637544971371309265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6671171091696647580872843 10006756637544971371309265)
                  ·
                    refine ⟨7505067478158728528481949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10006756637544971371309265 7505067478158728528481949)
                    ·
                      refine ⟨2814400304309523198180731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7505067478158728528481949 2814400304309523198180731)
                      ·
                        rfl

theorem cell23_5481025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_5481025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481025 prefixEnd_5481025 := by exact prefixLift 5481025
  have htrace : WordTrace (prefixWord ++ tailWord_5481025) baseStart_5481025 baseEnd_5481025 := by
    simpa [prefixWord, tailWord_5481025, baseEnd_5481025] using wordTrace_append hprefix tailTrace_5481025
  have hstable : (prefixWord ++ tailWord_5481025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481025).length < 2 ^ (prefixWord ++ tailWord_5481025).sum := by decide
  have hdescent : baseEnd_5481025 < baseStart_5481025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481090 : List Nat := [3, 4, 3, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5481090 : Nat := 118140960795 + 5481090 * 2 ^ 59
def prefixEnd_5481090 : Nat := 4983230072969 + 3 ^ 40 * 5481090 * 2
def baseEnd_5481090 : Nat := 2814433680552065443867933

theorem tailTrace_5481090 : CollatzResearch.WordTrace tailWord_5481090 prefixEnd_5481090 2814433680552065443867933 := by
  unfold tailWord_5481090
  simp only [CollatzResearch.WordTrace]
  refine ⟨49977943928238625122682181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133274517141969666993819149 49977943928238625122682181)
  ·
    refine ⟨9370864486544742210502909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49977943928238625122682181 9370864486544742210502909)
    ·
      refine ⟨3514074182454278328938591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9370864486544742210502909 3514074182454278328938591)
      ·
        refine ⟨5271111273681417493407887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514074182454278328938591 5271111273681417493407887)
        ·
          refine ⟨7906666910522126240111831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271111273681417493407887 7906666910522126240111831)
          ·
            refine ⟨11860000365783189360167747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7906666910522126240111831 11860000365783189360167747)
            ·
              refine ⟨17790000548674784040251621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11860000365783189360167747 17790000548674784040251621)
              ·
                refine ⟨3335625102876522007547179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17790000548674784040251621 3335625102876522007547179)
                ·
                  refine ⟨5003437654314783011320769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335625102876522007547179 5003437654314783011320769)
                  ·
                    refine ⟨3752578240736087258490577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5003437654314783011320769 3752578240736087258490577)
                    ·
                      refine ⟨2814433680552065443867933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3752578240736087258490577 2814433680552065443867933)
                      ·
                        rfl

theorem cell23_5481090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5481090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481090 prefixEnd_5481090 := by exact prefixLift 5481090
  have htrace : WordTrace (prefixWord ++ tailWord_5481090) baseStart_5481090 baseEnd_5481090 := by
    simpa [prefixWord, tailWord_5481090, baseEnd_5481090] using wordTrace_append hprefix tailTrace_5481090
  have hstable : (prefixWord ++ tailWord_5481090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481090).length < 2 ^ (prefixWord ++ tailWord_5481090).sum := by decide
  have hdescent : baseEnd_5481090 < baseStart_5481090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481112 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 2, 2, 2]
def baseStart_5481112 : Nat := 118140960795 + 5481112 * 2 ^ 59
def prefixEnd_5481112 : Nat := 4983230072969 + 3 ^ 40 * 5481112 * 2
def baseEnd_5481112 : Nat := 2814444977126464357792831

theorem tailTrace_5481112 : CollatzResearch.WordTrace tailWord_5481112 prefixEnd_5481112 2814444977126464357792831 := by
  unfold tailWord_5481112
  simp only [CollatzResearch.WordTrace]
  refine ⟨99956289059437399124014795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133275052079249865498686393 99956289059437399124014795)
  ·
    refine ⟨149934433589156098686022193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99956289059437399124014795 149934433589156098686022193)
    ·
      refine ⟨112450825191867074014516645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149934433589156098686022193 112450825191867074014516645)
      ·
        refine ⟨21084529723475076377721871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112450825191867074014516645 21084529723475076377721871)
        ·
          refine ⟨31626794585212614566582807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21084529723475076377721871 31626794585212614566582807)
          ·
            refine ⟨47440191877818921849874211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31626794585212614566582807 47440191877818921849874211)
            ·
              refine ⟨71160287816728382774811317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47440191877818921849874211 71160287816728382774811317)
              ·
                refine ⟨6671276982818285885138561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71160287816728382774811317 6671276982818285885138561)
                ·
                  refine ⟨5003457737113714413853921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6671276982818285885138561 5003457737113714413853921)
                  ·
                    refine ⟨3752593302835285810390441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5003457737113714413853921 3752593302835285810390441)
                    ·
                      refine ⟨2814444977126464357792831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3752593302835285810390441 2814444977126464357792831)
                      ·
                        rfl

theorem cell23_5481112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_5481112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481112 prefixEnd_5481112 := by exact prefixLift 5481112
  have htrace : WordTrace (prefixWord ++ tailWord_5481112) baseStart_5481112 baseEnd_5481112 := by
    simpa [prefixWord, tailWord_5481112, baseEnd_5481112] using wordTrace_append hprefix tailTrace_5481112
  have hstable : (prefixWord ++ tailWord_5481112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481112).length < 2 ^ (prefixWord ++ tailWord_5481112).sum := by decide
  have hdescent : baseEnd_5481112 < baseStart_5481112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481135 : List Nat := [1, 1, 2, 1, 2, 6, 2, 3, 5]
def baseStart_5481135 : Nat := 118140960795 + 5481135 * 2 ^ 59
def prefixEnd_5481135 : Nat := 4983230072969 + 3 ^ 40 * 5481135 * 2
def baseEnd_5481135 : Nat := 312717420797946418645025

theorem tailTrace_5481135 : CollatzResearch.WordTrace tailWord_5481135 prefixEnd_5481135 312717420797946418645025 := by
  unfold tailWord_5481135
  simp only [CollatzResearch.WordTrace]
  refine ⟨199913416997791473176116859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133275611331860982117411239 199913416997791473176116859)
  ·
    refine ⟨299870125496687209764175289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199913416997791473176116859 299870125496687209764175289)
    ·
      refine ⟨224902594122515407323131467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299870125496687209764175289 224902594122515407323131467)
      ·
        refine ⟨337353891183773110984697201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224902594122515407323131467 337353891183773110984697201)
        ·
          refine ⟨253015418387829833238522901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337353891183773110984697201 253015418387829833238522901)
          ·
            refine ⟨11860097736929523433055761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 253015418387829833238522901 11860097736929523433055761)
            ·
              refine ⟨8895073302697142574791821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11860097736929523433055761 8895073302697142574791821)
              ·
                refine ⟨3335652488511428465546933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8895073302697142574791821 3335652488511428465546933)
                ·
                  refine ⟨312717420797946418645025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3335652488511428465546933 312717420797946418645025)
                  ·
                    rfl

theorem cell23_5481135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 5].length) (baseStart_5481135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481135 prefixEnd_5481135 := by exact prefixLift 5481135
  have htrace : WordTrace (prefixWord ++ tailWord_5481135) baseStart_5481135 baseEnd_5481135 := by
    simpa [prefixWord, tailWord_5481135, baseEnd_5481135] using wordTrace_append hprefix tailTrace_5481135
  have hstable : (prefixWord ++ tailWord_5481135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481135).length < 2 ^ (prefixWord ++ tailWord_5481135).sum := by decide
  have hdescent : baseEnd_5481135 < baseStart_5481135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481148 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_5481148 : Nat := 118140960795 + 5481148 * 2 ^ 59
def prefixEnd_5481148 : Nat := 4983230072969 + 3 ^ 40 * 5481148 * 2
def baseEnd_5481148 : Nat := 938154487476675405647555

theorem tailTrace_5481148 : CollatzResearch.WordTrace tailWord_5481148 prefixEnd_5481148 938154487476675405647555 := by
  unfold tailWord_5481148
  simp only [CollatzResearch.WordTrace]
  refine ⟨99956945573372188198170049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133275927431162917597560065 99956945573372188198170049)
  ·
    refine ⟨74967709180029141148627537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99956945573372188198170049 74967709180029141148627537)
    ·
      refine ⟨56225781885021855861470653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74967709180029141148627537 56225781885021855861470653)
      ·
        refine ⟨21084668206883195948051495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56225781885021855861470653 21084668206883195948051495)
        ·
          refine ⟨31627002310324793922077243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21084668206883195948051495 31627002310324793922077243)
          ·
            refine ⟨47440503465487190883115865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31627002310324793922077243 47440503465487190883115865)
            ·
              refine ⟨35580377599115393162336899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47440503465487190883115865 35580377599115393162336899)
              ·
                refine ⟨53370566398673089743505349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35580377599115393162336899 53370566398673089743505349)
                ·
                  refine ⟨10006981199751204326907253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53370566398673089743505349 10006981199751204326907253)
                  ·
                    refine ⟨938154487476675405647555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10006981199751204326907253 938154487476675405647555)
                    ·
                      rfl

theorem cell23_5481148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_5481148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481148 prefixEnd_5481148 := by exact prefixLift 5481148
  have htrace : WordTrace (prefixWord ++ tailWord_5481148) baseStart_5481148 baseEnd_5481148 := by
    simpa [prefixWord, tailWord_5481148, baseEnd_5481148] using wordTrace_append hprefix tailTrace_5481148
  have hstable : (prefixWord ++ tailWord_5481148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481148).length < 2 ^ (prefixWord ++ tailWord_5481148).sum := by decide
  have hdescent : baseEnd_5481148 < baseStart_5481148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481208 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 6]
def baseStart_5481208 : Nat := 118140960795 + 5481208 * 2 ^ 59
def prefixEnd_5481208 : Nat := 4983230072969 + 3 ^ 40 * 5481208 * 2
def baseEnd_5481208 : Nat := 312721585696588442465821

theorem tailTrace_5481208 : CollatzResearch.WordTrace tailWord_5481208 prefixEnd_5481208 312721585696588442465821 := by
  unfold tailWord_5481208
  simp only [CollatzResearch.WordTrace]
  refine ⟨99958039763263503321762139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133277386351018004429016185 99958039763263503321762139)
  ·
    refine ⟨149937059644895254982643209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99958039763263503321762139 149937059644895254982643209)
    ·
      refine ⟨112452794733671441236982407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149937059644895254982643209 112452794733671441236982407)
      ·
        refine ⟨168679192100507161855473611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112452794733671441236982407 168679192100507161855473611)
        ·
          refine ⟨253018788150760742783210417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168679192100507161855473611 253018788150760742783210417)
          ·
            refine ⟨189764091113070557087407813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253018788150760742783210417 189764091113070557087407813)
            ·
              refine ⟨35580767083700729453888965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189764091113070557087407813 35580767083700729453888965)
              ·
                refine ⟨6671393828193886772604181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35580767083700729453888965 6671393828193886772604181)
                ·
                  refine ⟨312721585696588442465821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6671393828193886772604181 312721585696588442465821)
                  ·
                    rfl

theorem cell23_5481208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 6].length) (baseStart_5481208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481208 prefixEnd_5481208 := by exact prefixLift 5481208
  have htrace : WordTrace (prefixWord ++ tailWord_5481208) baseStart_5481208 baseEnd_5481208 := by
    simpa [prefixWord, tailWord_5481208, baseEnd_5481208] using wordTrace_append hprefix tailTrace_5481208
  have hstable : (prefixWord ++ tailWord_5481208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481208).length < 2 ^ (prefixWord ++ tailWord_5481208).sum := by decide
  have hdescent : baseEnd_5481208 < baseStart_5481208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481212 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_5481212 : Nat := 118140960795 + 5481212 * 2 ^ 59
def prefixEnd_5481212 : Nat := 4983230072969 + 3 ^ 40 * 5481212 * 2
def baseEnd_5481212 : Nat := 938165441730637988847457

theorem tailTrace_5481212 : CollatzResearch.WordTrace tailWord_5481212 prefixEnd_5481212 938165441730637988847457 := by
  unfold tailWord_5481212
  simp only [CollatzResearch.WordTrace]
  refine ⟨99958112709256257663334945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133277483612341676884446593 99958112709256257663334945)
  ·
    refine ⟨74968584531942193247501209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99958112709256257663334945 74968584531942193247501209)
    ·
      refine ⟨56226438398956644935625907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74968584531942193247501209 56226438398956644935625907)
      ·
        refine ⟨84339657598434967403438861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56226438398956644935625907 84339657598434967403438861)
        ·
          refine ⟨31627371599413112776289573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84339657598434967403438861 31627371599413112776289573)
          ·
            refine ⟨5930132174889958645554295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31627371599413112776289573 5930132174889958645554295)
            ·
              refine ⟨8895198262334937968331443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930132174889958645554295 8895198262334937968331443)
              ·
                refine ⟨13342797393502406952497165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895198262334937968331443 13342797393502406952497165)
                ·
                  refine ⟨5003549022563402607186437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13342797393502406952497165 5003549022563402607186437)
                  ·
                    refine ⟨938165441730637988847457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003549022563402607186437 938165441730637988847457)
                    ·
                      rfl

theorem cell23_5481212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_5481212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481212 prefixEnd_5481212 := by exact prefixLift 5481212
  have htrace : WordTrace (prefixWord ++ tailWord_5481212) baseStart_5481212 baseEnd_5481212 := by
    simpa [prefixWord, tailWord_5481212, baseEnd_5481212] using wordTrace_append hprefix tailTrace_5481212
  have hstable : (prefixWord ++ tailWord_5481212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481212).length < 2 ^ (prefixWord ++ tailWord_5481212).sum := by decide
  have hdescent : baseEnd_5481212 < baseStart_5481212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481225 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 6]
def baseStart_5481225 : Nat := 118140960795 + 5481225 * 2 ^ 59
def prefixEnd_5481225 : Nat := 4983230072969 + 3 ^ 40 * 5481225 * 2
def baseEnd_5481225 : Nat := 312722555604491379519979

theorem tailTrace_5481225 : CollatzResearch.WordTrace tailWord_5481225 prefixEnd_5481225 312722555604491379519979 := by
  unfold tailWord_5481225
  simp only [CollatzResearch.WordTrace]
  refine ⟨199916699567465418546893129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133277799711643612364595419 199916699567465418546893129)
  ·
    refine ⟨149937524675599063910169847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199916699567465418546893129 149937524675599063910169847)
    ·
      refine ⟨224906287013398595865254771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149937524675599063910169847 224906287013398595865254771)
      ·
        refine ⟨337359430520097893797882157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224906287013398595865254771 337359430520097893797882157)
        ·
          refine ⟨126509786445036710174205809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337359430520097893797882157 126509786445036710174205809)
          ·
            refine ⟨94882339833777532630654357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126509786445036710174205809 94882339833777532630654357)
            ·
              refine ⟨4447609679708321842061923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94882339833777532630654357 4447609679708321842061923)
              ·
                refine ⟨6671414519562482763092885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447609679708321842061923 6671414519562482763092885)
                ·
                  refine ⟨312722555604491379519979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6671414519562482763092885 312722555604491379519979)
                  ·
                    rfl

theorem cell23_5481225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 6].length) (baseStart_5481225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481225 prefixEnd_5481225 := by exact prefixLift 5481225
  have htrace : WordTrace (prefixWord ++ tailWord_5481225) baseStart_5481225 baseEnd_5481225 := by
    simpa [prefixWord, tailWord_5481225, baseEnd_5481225] using wordTrace_append hprefix tailTrace_5481225
  have hstable : (prefixWord ++ tailWord_5481225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481225).length < 2 ^ (prefixWord ++ tailWord_5481225).sum := by decide
  have hdescent : baseEnd_5481225 < baseStart_5481225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481235 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 3]
def baseStart_5481235 : Nat := 118140960795 + 5481235 * 2 ^ 59
def prefixEnd_5481235 : Nat := 4983230072969 + 3 ^ 40 * 5481235 * 2
def baseEnd_5481235 : Nat := 2814508135246967376554765

theorem tailTrace_5481235 : CollatzResearch.WordTrace tailWord_5481235 prefixEnd_5481235 2814508135246967376554765 := by
  unfold tailWord_5481235
  simp only [CollatzResearch.WordTrace]
  refine ⟨199917064297429190254757159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133278042864952793503171439 199917064297429190254757159)
  ·
    refine ⟨299875596446143785382135739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199917064297429190254757159 299875596446143785382135739)
    ·
      refine ⟨449813394669215678073203609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299875596446143785382135739 449813394669215678073203609)
      ·
        refine ⟨337360046001911758554902707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449813394669215678073203609 337360046001911758554902707)
        ·
          refine ⟨506040069002867637832354061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337360046001911758554902707 506040069002867637832354061)
          ·
            refine ⟨189765025876075364187132773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506040069002867637832354061 189765025876075364187132773)
            ·
              refine ⟨35580942351764130785087395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189765025876075364187132773 35580942351764130785087395)
              ·
                refine ⟨53371413527646196177631093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35580942351764130785087395 53371413527646196177631093)
                ·
                  refine ⟨5003570018216830891652915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53371413527646196177631093 5003570018216830891652915)
                  ·
                    refine ⟨7505355027325246337479373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5003570018216830891652915 7505355027325246337479373)
                    ·
                      refine ⟨2814508135246967376554765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7505355027325246337479373 2814508135246967376554765)
                      ·
                        rfl

theorem cell23_5481235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 1, 3].length) (baseStart_5481235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481235 prefixEnd_5481235 := by exact prefixLift 5481235
  have htrace : WordTrace (prefixWord ++ tailWord_5481235) baseStart_5481235 baseEnd_5481235 := by
    simpa [prefixWord, tailWord_5481235, baseEnd_5481235] using wordTrace_append hprefix tailTrace_5481235
  have hstable : (prefixWord ++ tailWord_5481235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481235).length < 2 ^ (prefixWord ++ tailWord_5481235).sum := by decide
  have hdescent : baseEnd_5481235 < baseStart_5481235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481305 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_5481305 : Nat := 118140960795 + 5481305 * 2 ^ 59
def prefixEnd_5481305 : Nat := 4983230072969 + 3 ^ 40 * 5481305 * 2
def baseEnd_5481305 : Nat := 2814544078892782102679443

theorem tailTrace_5481305 : CollatzResearch.WordTrace tailWord_5481305 prefixEnd_5481305 2814544078892782102679443 := by
  unfold tailWord_5481305
  simp only [CollatzResearch.WordTrace]
  refine ⟨199919617407175592209805369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133279744938117061473203579 199919617407175592209805369)
  ·
    refine ⟨149939713055381694157354027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199919617407175592209805369 149939713055381694157354027)
    ·
      refine ⟨224909569583072541236031041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149939713055381694157354027 224909569583072541236031041)
      ·
        refine ⟨168682177187304405927023281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224909569583072541236031041 168682177187304405927023281)
        ·
          refine ⟨126511632890478304445267461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168682177187304405927023281 126511632890478304445267461)
          ·
            refine ⟨23720931166964682083487649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126511632890478304445267461 23720931166964682083487649)
            ·
              refine ⟨17790698375223511562615737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23720931166964682083487649 17790698375223511562615737)
              ·
                refine ⟨13343023781417633671961803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17790698375223511562615737 13343023781417633671961803)
                ·
                  refine ⟨20014535672126450507942705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13343023781417633671961803 20014535672126450507942705)
                  ·
                    refine ⟨15010901754094837880957029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20014535672126450507942705 15010901754094837880957029)
                    ·
                      refine ⟨2814544078892782102679443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15010901754094837880957029 2814544078892782102679443)
                      ·
                        rfl

theorem cell23_5481305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_5481305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481305 prefixEnd_5481305 := by exact prefixLift 5481305
  have htrace : WordTrace (prefixWord ++ tailWord_5481305) baseStart_5481305 baseEnd_5481305 := by
    simpa [prefixWord, tailWord_5481305, baseEnd_5481305] using wordTrace_append hprefix tailTrace_5481305
  have hstable : (prefixWord ++ tailWord_5481305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481305).length < 2 ^ (prefixWord ++ tailWord_5481305).sum := by decide
  have hdescent : baseEnd_5481305 < baseStart_5481305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481312 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3]
def baseStart_5481312 : Nat := 118140960795 + 5481312 * 2 ^ 59
def prefixEnd_5481312 : Nat := 4983230072969 + 3 ^ 40 * 5481312 * 2
def baseEnd_5481312 : Nat := 2814547673257363575291911

theorem tailTrace_5481312 : CollatzResearch.WordTrace tailWord_5481312 prefixEnd_5481312 2814547673257363575291911 := by
  unfold tailWord_5481312
  simp only [CollatzResearch.WordTrace]
  refine ⟨99959936359075116202655095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133279915145433488270206793 99959936359075116202655095)
  ·
    refine ⟨149939904538612674303982643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99959936359075116202655095 149939904538612674303982643)
    ·
      refine ⟨224909856807919011455973965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149939904538612674303982643 224909856807919011455973965)
      ·
        refine ⟨84341196302969629295990237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224909856807919011455973965 84341196302969629295990237)
        ·
          refine ⟨31627948613613610985996339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84341196302969629295990237 31627948613613610985996339)
          ·
            refine ⟨47441922920420416478994509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31627948613613610985996339 47441922920420416478994509)
            ·
              refine ⟨17790721095157656179622941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47441922920420416478994509 17790721095157656179622941)
              ·
                refine ⟨6671520410684121067358603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17790721095157656179622941 6671520410684121067358603)
                ·
                  refine ⟨10007280616026181601037905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6671520410684121067358603 10007280616026181601037905)
                  ·
                    refine ⟨7505460462019636200778429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10007280616026181601037905 7505460462019636200778429)
                    ·
                      refine ⟨2814547673257363575291911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7505460462019636200778429 2814547673257363575291911)
                      ·
                        rfl

theorem cell23_5481312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_5481312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481312 prefixEnd_5481312 := by exact prefixLift 5481312
  have htrace : WordTrace (prefixWord ++ tailWord_5481312) baseStart_5481312 baseEnd_5481312 := by
    simpa [prefixWord, tailWord_5481312, baseEnd_5481312] using wordTrace_append hprefix tailTrace_5481312
  have hstable : (prefixWord ++ tailWord_5481312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481312).length < 2 ^ (prefixWord ++ tailWord_5481312).sum := by decide
  have hdescent : baseEnd_5481312 < baseStart_5481312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481319 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 2, 4]
def baseStart_5481319 : Nat := 118140960795 + 5481319 * 2 ^ 59
def prefixEnd_5481319 : Nat := 4983230072969 + 3 ^ 40 * 5481319 * 2
def baseEnd_5481319 : Nat := 938183755873981682634793

theorem tailTrace_5481319 : CollatzResearch.WordTrace tailWord_5481319 prefixEnd_5481319 938183755873981682634793 := by
  unfold tailWord_5481319
  simp only [CollatzResearch.WordTrace]
  refine ⟨199920128029124872600815011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133280085352749915067210007 199920128029124872600815011)
  ·
    refine ⟨299880192043687308901222517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199920128029124872600815011 299880192043687308901222517)
    ·
      refine ⟨28113768004095685209489611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 299880192043687308901222517 28113768004095685209489611)
      ·
        refine ⟨42170652006143527814234417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28113768004095685209489611 42170652006143527814234417)
        ·
          refine ⟨31627989004607645860675813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42170652006143527814234417 31627989004607645860675813)
          ·
            refine ⟨5930247938363933598876715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31627989004607645860675813 5930247938363933598876715)
            ·
              refine ⟨8895371907545900398315073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930247938363933598876715 8895371907545900398315073)
              ·
                refine ⟨6671528930659425298736305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8895371907545900398315073 6671528930659425298736305)
                ·
                  refine ⟨5003646697994568974052229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6671528930659425298736305 5003646697994568974052229)
                  ·
                    refine ⟨938183755873981682634793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003646697994568974052229 938183755873981682634793)
                    ·
                      rfl

theorem cell23_5481319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_5481319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481319 prefixEnd_5481319 := by exact prefixLift 5481319
  have htrace : WordTrace (prefixWord ++ tailWord_5481319) baseStart_5481319 baseEnd_5481319 := by
    simpa [prefixWord, tailWord_5481319, baseEnd_5481319] using wordTrace_append hprefix tailTrace_5481319
  have hstable : (prefixWord ++ tailWord_5481319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481319).length < 2 ^ (prefixWord ++ tailWord_5481319).sum := by decide
  have hdescent : baseEnd_5481319 < baseStart_5481319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481328 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 9]
def baseStart_5481328 : Nat := 118140960795 + 5481328 * 2 ^ 59
def prefixEnd_5481328 : Nat := 4983230072969 + 3 ^ 40 * 5481328 * 2
def baseEnd_5481328 : Nat := 938185296315945170897279

theorem tailTrace_5481328 : CollatzResearch.WordTrace tailWord_5481328 prefixEnd_5481328 938185296315945170897279 := by
  unfold tailWord_5481328
  simp only [CollatzResearch.WordTrace]
  refine ⟨99960228143046133568946319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133280304190728178091928425 99960228143046133568946319)
  ·
    refine ⟨149940342214569200353419479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99960228143046133568946319 149940342214569200353419479)
    ·
      refine ⟨224910513321853800530129219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149940342214569200353419479 224910513321853800530129219)
      ·
        refine ⟨337365769982780700795193829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224910513321853800530129219 337365769982780700795193829)
        ·
          refine ⟨63256081871771381399098843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 337365769982780700795193829 63256081871771381399098843)
          ·
            refine ⟨94884122807657072098648265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63256081871771381399098843 94884122807657072098648265)
            ·
              refine ⟨71163092105742804073986199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94884122807657072098648265 71163092105742804073986199)
              ·
                refine ⟨106744638158614206110979299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71163092105742804073986199 106744638158614206110979299)
                ·
                  refine ⟨160116957237921309166468949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106744638158614206110979299 160116957237921309166468949)
                  ·
                    refine ⟨938185296315945170897279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 160116957237921309166468949 938185296315945170897279)
                    ·
                      rfl

theorem cell23_5481328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_5481328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481328 prefixEnd_5481328 := by exact prefixLift 5481328
  have htrace : WordTrace (prefixWord ++ tailWord_5481328) baseStart_5481328 baseEnd_5481328 := by
    simpa [prefixWord, tailWord_5481328, baseEnd_5481328] using wordTrace_append hprefix tailTrace_5481328
  have hstable : (prefixWord ++ tailWord_5481328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481328).length < 2 ^ (prefixWord ++ tailWord_5481328).sum := by decide
  have hdescent : baseEnd_5481328 < baseStart_5481328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481385 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 3]
def baseStart_5481385 : Nat := 118140960795 + 5481385 * 2 ^ 59
def prefixEnd_5481385 : Nat := 4983230072969 + 3 ^ 40 * 5481385 * 2
def baseEnd_5481385 : Nat := 2814585157345141789679075

theorem tailTrace_5481385 : CollatzResearch.WordTrace tailWord_5481385 prefixEnd_5481385 2814585157345141789679075 := by
  unfold tailWord_5481385
  simp only [CollatzResearch.WordTrace]
  refine ⟨199922535246885765872717609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133281690164590510581811739 199922535246885765872717609)
  ·
    refine ⟨149941901435164324404538207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199922535246885765872717609 149941901435164324404538207)
    ·
      refine ⟨224912852152746486606807311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149941901435164324404538207 224912852152746486606807311)
      ·
        refine ⟨337369278229119729910210967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224912852152746486606807311 337369278229119729910210967)
        ·
          refine ⟨506053917343679594865316451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337369278229119729910210967 506053917343679594865316451)
          ·
            refine ⟨759080876015519392297974677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506053917343679594865316451 759080876015519392297974677)
            ·
              refine ⟨35581916063227471513967563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 759080876015519392297974677 35581916063227471513967563)
              ·
                refine ⟨53372874094841207270951345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35581916063227471513967563 53372874094841207270951345)
                ·
                  refine ⟨40029655571130905453213509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53372874094841207270951345 40029655571130905453213509)
                  ·
                    refine ⟨7505560419587044772477533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40029655571130905453213509 7505560419587044772477533)
                    ·
                      refine ⟨2814585157345141789679075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7505560419587044772477533 2814585157345141789679075)
                      ·
                        rfl

theorem cell23_5481385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_5481385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481385 prefixEnd_5481385 := by exact prefixLift 5481385
  have htrace : WordTrace (prefixWord ++ tailWord_5481385) baseStart_5481385 baseEnd_5481385 := by
    simpa [prefixWord, tailWord_5481385, baseEnd_5481385] using wordTrace_append hprefix tailTrace_5481385
  have hstable : (prefixWord ++ tailWord_5481385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481385).length < 2 ^ (prefixWord ++ tailWord_5481385).sum := by decide
  have hdescent : baseEnd_5481385 < baseStart_5481385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481393 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 2, 1, 3]
def baseStart_5481393 : Nat := 118140960795 + 5481393 * 2 ^ 59
def prefixEnd_5481393 : Nat := 4983230072969 + 3 ^ 40 * 5481393 * 2
def baseEnd_5481393 : Nat := 2814589265190377758379039

theorem tailTrace_5481393 : CollatzResearch.WordTrace tailWord_5481393 prefixEnd_5481393 2814589265190377758379039 := by
  unfold tailWord_5481393
  simp only [CollatzResearch.WordTrace]
  refine ⟨199922827030856783239008833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133281884687237855492672555 199922827030856783239008833)
  ·
    refine ⟨149942120273142587429256625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199922827030856783239008833 149942120273142587429256625)
    ·
      refine ⟨112456590204856940571942469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149942120273142587429256625 112456590204856940571942469)
      ·
        refine ⟨21085610663410676357239213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112456590204856940571942469 21085610663410676357239213)
        ·
          refine ⟨7907103998779003633964705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21085610663410676357239213 7907103998779003633964705)
          ·
            refine ⟨5930327999084252725473529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7907103998779003633964705 5930327999084252725473529)
            ·
              refine ⟨4447745999313189544105147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5930327999084252725473529 4447745999313189544105147)
              ·
                refine ⟨6671618998969784316157721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447745999313189544105147 6671618998969784316157721)
                ·
                  refine ⟨5003714249227338237118291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6671618998969784316157721 5003714249227338237118291)
                  ·
                    refine ⟨7505571373841007355677437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5003714249227338237118291 7505571373841007355677437)
                    ·
                      refine ⟨2814589265190377758379039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7505571373841007355677437 2814589265190377758379039)
                      ·
                        rfl

theorem cell23_5481393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_5481393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481393 prefixEnd_5481393 := by exact prefixLift 5481393
  have htrace : WordTrace (prefixWord ++ tailWord_5481393) baseStart_5481393 baseEnd_5481393 := by
    simpa [prefixWord, tailWord_5481393, baseEnd_5481393] using wordTrace_append hprefix tailTrace_5481393
  have hstable : (prefixWord ++ tailWord_5481393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481393).length < 2 ^ (prefixWord ++ tailWord_5481393).sum := by decide
  have hdescent : baseEnd_5481393 < baseStart_5481393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481439 : List Nat := [1, 1, 2, 3, 5, 1, 1, 4, 5]
def baseStart_5481439 : Nat := 118140960795 + 5481439 * 2 ^ 59
def prefixEnd_5481439 : Nat := 4983230072969 + 3 ^ 40 * 5481439 * 2
def baseEnd_5481439 : Nat := 312734765033387175378203

theorem tailTrace_5481439 : CollatzResearch.WordTrace tailWord_5481439 prefixEnd_5481439 312734765033387175378203 := by
  unfold tailWord_5481439
  simp only [CollatzResearch.WordTrace]
  refine ⟨199924504788690133095183371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133283003192460088730122247 199924504788690133095183371)
  ·
    refine ⟨299886757183035199642775057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199924504788690133095183371 299886757183035199642775057)
    ·
      refine ⟨224915067887276399732081293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299886757183035199642775057 224915067887276399732081293)
      ·
        refine ⟨84343150457728649899530485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224915067887276399732081293 84343150457728649899530485)
        ·
          refine ⟨7907170355412060928080983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84343150457728649899530485 7907170355412060928080983)
          ·
            refine ⟨11860755533118091392121475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907170355412060928080983 11860755533118091392121475)
            ·
              refine ⟨17791133299677137088182213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11860755533118091392121475 17791133299677137088182213)
              ·
                refine ⟨3335837493689463204034165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17791133299677137088182213 3335837493689463204034165)
                ·
                  refine ⟨312734765033387175378203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3335837493689463204034165 312734765033387175378203)
                  ·
                    rfl

theorem cell23_5481439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 5].length) (baseStart_5481439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481439 prefixEnd_5481439 := by exact prefixLift 5481439
  have htrace : WordTrace (prefixWord ++ tailWord_5481439) baseStart_5481439 baseEnd_5481439 := by
    simpa [prefixWord, tailWord_5481439, baseEnd_5481439] using wordTrace_append hprefix tailTrace_5481439
  have hstable : (prefixWord ++ tailWord_5481439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481439).length < 2 ^ (prefixWord ++ tailWord_5481439).sum := by decide
  have hdescent : baseEnd_5481439 < baseStart_5481439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481515 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6]
def baseStart_5481515 : Nat := 118140960795 + 5481515 * 2 ^ 59
def prefixEnd_5481515 : Nat := 4983230072969 + 3 ^ 40 * 5481515 * 2
def baseEnd_5481515 : Nat := 2814651909830226281053477

theorem tailTrace_5481515 : CollatzResearch.WordTrace tailWord_5481515 prefixEnd_5481515 2814651909830226281053477 := by
  unfold tailWord_5481515
  simp only [CollatzResearch.WordTrace]
  refine ⟨199927276736414798074949999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133284851157609865383299999 199927276736414798074949999)
  ·
    refine ⟨299890915104622197112424999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199927276736414798074949999 299890915104622197112424999)
    ·
      refine ⟨449836372656933295668637499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299890915104622197112424999 449836372656933295668637499)
      ·
        refine ⟨674754558985399943502956249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449836372656933295668637499 674754558985399943502956249)
        ·
          refine ⟨506065919239049957627217187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674754558985399943502956249 506065919239049957627217187)
          ·
            refine ⟨759098878858574936440825781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506065919239049957627217187 759098878858574936440825781)
            ·
              refine ⟨71165519892991400291327417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 759098878858574936440825781 71165519892991400291327417)
              ·
                refine ⟨53374139919743550218495563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71165519892991400291327417 53374139919743550218495563)
                ·
                  refine ⟨80061209879615325327743345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53374139919743550218495563 80061209879615325327743345)
                  ·
                    refine ⟨60045907409711493995807509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80061209879615325327743345 60045907409711493995807509)
                    ·
                      refine ⟨2814651909830226281053477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60045907409711493995807509 2814651909830226281053477)
                      ·
                        rfl

theorem cell23_5481515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_5481515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481515 prefixEnd_5481515 := by exact prefixLift 5481515
  have htrace : WordTrace (prefixWord ++ tailWord_5481515) baseStart_5481515 baseEnd_5481515 := by
    simpa [prefixWord, tailWord_5481515, baseEnd_5481515] using wordTrace_append hprefix tailTrace_5481515
  have hstable : (prefixWord ++ tailWord_5481515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481515).length < 2 ^ (prefixWord ++ tailWord_5481515).sum := by decide
  have hdescent : baseEnd_5481515 < baseStart_5481515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481522 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_5481522 : Nat := 118140960795 + 5481522 * 2 ^ 59
def prefixEnd_5481522 : Nat := 4983230072969 + 3 ^ 40 * 5481522 * 2
def baseEnd_5481522 : Nat := 2814655504194807753665945

theorem tailTrace_5481522 : CollatzResearch.WordTrace tailWord_5481522 prefixEnd_5481522 2814655504194807753665945 := by
  unfold tailWord_5481522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49981883011847359567613705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133285021364926292180303213 49981883011847359567613705)
  ·
    refine ⟨37486412258885519675710279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49981883011847359567613705 37486412258885519675710279)
    ·
      refine ⟨56229618388328279513565419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37486412258885519675710279 56229618388328279513565419)
      ·
        refine ⟨84344427582492419270348129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56229618388328279513565419 84344427582492419270348129)
        ·
          refine ⟨63258320686869314452761097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84344427582492419270348129 63258320686869314452761097)
          ·
            refine ⟨47443740515151985839570823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63258320686869314452761097 47443740515151985839570823)
            ·
              refine ⟨71165610772727978759356235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47443740515151985839570823 71165610772727978759356235)
              ·
                refine ⟨106748416159091968139034353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71165610772727978759356235 106748416159091968139034353)
                ·
                  refine ⟨80061312119318976104275765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106748416159091968139034353 80061312119318976104275765)
                  ·
                    refine ⟨7505748011186154009775853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80061312119318976104275765 7505748011186154009775853)
                    ·
                      refine ⟨2814655504194807753665945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7505748011186154009775853 2814655504194807753665945)
                      ·
                        rfl

theorem cell23_5481522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_5481522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481522 prefixEnd_5481522 := by exact prefixLift 5481522
  have htrace : WordTrace (prefixWord ++ tailWord_5481522) baseStart_5481522 baseEnd_5481522 := by
    simpa [prefixWord, tailWord_5481522, baseEnd_5481522] using wordTrace_append hprefix tailTrace_5481522
  have hstable : (prefixWord ++ tailWord_5481522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481522).length < 2 ^ (prefixWord ++ tailWord_5481522).sum := by decide
  have hdescent : baseEnd_5481522 < baseStart_5481522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481533 : List Nat := [1, 4, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_5481533 : Nat := 118140960795 + 5481533 * 2 ^ 59
def prefixEnd_5481533 : Nat := 4983230072969 + 3 ^ 40 * 5481533 * 2
def baseEnd_5481533 : Nat := 938220384160669070209465

theorem tailTrace_5481533 : CollatzResearch.WordTrace tailWord_5481533 prefixEnd_5481533 938220384160669070209465 := by
  unfold tailWord_5481533
  simp only [CollatzResearch.WordTrace]
  refine ⟨199927933250349587149105253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133285288833566391432736835 199927933250349587149105253)
  ·
    refine ⟨37486487484440547590457235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199927933250349587149105253 37486487484440547590457235)
    ·
      refine ⟨56229731226660821385685853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37486487484440547590457235 56229731226660821385685853)
      ·
        refine ⟨21086149209997808019632195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56229731226660821385685853 21086149209997808019632195)
        ·
          refine ⟨31629223814996712029448293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21086149209997808019632195 31629223814996712029448293)
          ·
            refine ⟨5930479465311883505521555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31629223814996712029448293 5930479465311883505521555)
            ·
              refine ⟨8895719197967825258282333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930479465311883505521555 8895719197967825258282333)
              ·
                refine ⟨3335894699237934471855875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8895719197967825258282333 3335894699237934471855875)
                ·
                  refine ⟨5003842048856901707783813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335894699237934471855875 5003842048856901707783813)
                  ·
                    refine ⟨938220384160669070209465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5003842048856901707783813 938220384160669070209465)
                    ·
                      rfl

theorem cell23_5481533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_5481533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481533 prefixEnd_5481533 := by exact prefixLift 5481533
  have htrace : WordTrace (prefixWord ++ tailWord_5481533) baseStart_5481533 baseEnd_5481533 := by
    simpa [prefixWord, tailWord_5481533, baseEnd_5481533] using wordTrace_append hprefix tailTrace_5481533
  have hstable : (prefixWord ++ tailWord_5481533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481533).length < 2 ^ (prefixWord ++ tailWord_5481533).sum := by decide
  have hdescent : baseEnd_5481533 < baseStart_5481533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481556 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_5481556 : Nat := 118140960795 + 5481556 * 2 ^ 59
def prefixEnd_5481556 : Nat := 4983230072969 + 3 ^ 40 * 5481556 * 2
def baseEnd_5481556 : Nat := 2814672962537060620640789

theorem tailTrace_5481556 : CollatzResearch.WordTrace tailWord_5481556 prefixEnd_5481556 2814672962537060620640789 := by
  unfold tailWord_5481556
  simp only [CollatzResearch.WordTrace]
  refine ⟨99964386064633131038596261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133285848086177508051461681 99964386064633131038596261)
  ·
    refine ⟨18743322387118712069736799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99964386064633131038596261 18743322387118712069736799)
    ·
      refine ⟨28114983580678068104605199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18743322387118712069736799 28114983580678068104605199)
      ·
        refine ⟨42172475371017102156907799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28114983580678068104605199 42172475371017102156907799)
        ·
          refine ⟨63258713056525653235361699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42172475371017102156907799 63258713056525653235361699)
          ·
            refine ⟨94888069584788479853042549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63258713056525653235361699 94888069584788479853042549)
            ·
              refine ⟨8895756523573919986222739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94888069584788479853042549 8895756523573919986222739)
              ·
                refine ⟨13343634785360879979334109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895756523573919986222739 13343634785360879979334109)
                ·
                  refine ⟨5003863044510329992250291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13343634785360879979334109 5003863044510329992250291)
                  ·
                    refine ⟨7505794566765494988375437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5003863044510329992250291 7505794566765494988375437)
                    ·
                      refine ⟨2814672962537060620640789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7505794566765494988375437 2814672962537060620640789)
                      ·
                        rfl

theorem cell23_5481556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_5481556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481556 prefixEnd_5481556 := by exact prefixLift 5481556
  have htrace : WordTrace (prefixWord ++ tailWord_5481556) baseStart_5481556 baseEnd_5481556 := by
    simpa [prefixWord, tailWord_5481556, baseEnd_5481556] using wordTrace_append hprefix tailTrace_5481556
  have hstable : (prefixWord ++ tailWord_5481556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481556).length < 2 ^ (prefixWord ++ tailWord_5481556).sum := by decide
  have hdescent : baseEnd_5481556 < baseStart_5481556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481572 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_5481572 : Nat := 118140960795 + 5481572 * 2 ^ 59
def prefixEnd_5481572 : Nat := 4983230072969 + 3 ^ 40 * 5481572 * 2
def baseEnd_5481572 : Nat := 938227059409177519346905

theorem tailTrace_5481572 : CollatzResearch.WordTrace tailWord_5481572 prefixEnd_5481572 938227059409177519346905 := by
  unfold tailWord_5481572
  simp only [CollatzResearch.WordTrace]
  refine ⟨99964677848604148404887485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133286237131472197873183313 99964677848604148404887485)
  ·
    refine ⟨37486754193226555651832807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99964677848604148404887485 37486754193226555651832807)
    ·
      refine ⟨56230131289839833477749211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37486754193226555651832807 56230131289839833477749211)
      ·
        refine ⟨84345196934759750216623817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56230131289839833477749211 84345196934759750216623817)
        ·
          refine ⟨63258897701069812662467863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84345196934759750216623817 63258897701069812662467863)
          ·
            refine ⟨94888346551604718993701795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63258897701069812662467863 94888346551604718993701795)
            ·
              refine ⟨142332519827407078490552693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94888346551604718993701795 142332519827407078490552693)
              ·
                refine ⟨13343673733819413608489315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142332519827407078490552693 13343673733819413608489315)
                ·
                  refine ⟨20015510600729120412733973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13343673733819413608489315 20015510600729120412733973)
                  ·
                    refine ⟨938227059409177519346905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20015510600729120412733973 938227059409177519346905)
                    ·
                      rfl

theorem cell23_5481572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_5481572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481572 prefixEnd_5481572 := by exact prefixLift 5481572
  have htrace : WordTrace (prefixWord ++ tailWord_5481572) baseStart_5481572 baseEnd_5481572 := by
    simpa [prefixWord, tailWord_5481572, baseEnd_5481572] using wordTrace_append hprefix tailTrace_5481572
  have hstable : (prefixWord ++ tailWord_5481572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481572).length < 2 ^ (prefixWord ++ tailWord_5481572).sum := by decide
  have hdescent : baseEnd_5481572 < baseStart_5481572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481576 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 3, 5]
def baseStart_5481576 : Nat := 118140960795 + 5481576 * 2 ^ 59
def prefixEnd_5481576 : Nat := 4983230072969 + 3 ^ 40 * 5481576 * 2
def baseEnd_5481576 : Nat := 938227744050050180796899

theorem tailTrace_5481576 : CollatzResearch.WordTrace tailWord_5481576 prefixEnd_5481576 938227744050050180796899 := by
  unfold tailWord_5481576
  simp only [CollatzResearch.WordTrace]
  refine ⟨99964750794596902746460291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133286334392795870328613721 99964750794596902746460291)
  ·
    refine ⟨149947126191895354119690437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99964750794596902746460291 149947126191895354119690437)
    ·
      refine ⟨28115086160980378897441957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149947126191895354119690437 28115086160980378897441957)
      ·
        refine ⟨5271578655183821043270367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28115086160980378897441957 5271578655183821043270367)
        ·
          refine ⟨7907367982775731564905551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271578655183821043270367 7907367982775731564905551)
          ·
            refine ⟨11861051974163597347358327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907367982775731564905551 11861051974163597347358327)
            ·
              refine ⟨17791577961245396021037491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11861051974163597347358327 17791577961245396021037491)
              ·
                refine ⟨26687366941868094031556237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17791577961245396021037491 26687366941868094031556237)
                ·
                  refine ⟨10007762603200535261833589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26687366941868094031556237 10007762603200535261833589)
                  ·
                    refine ⟨938227744050050180796899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10007762603200535261833589 938227744050050180796899)
                    ·
                      rfl

theorem cell23_5481576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_5481576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481576 prefixEnd_5481576 := by exact prefixLift 5481576
  have htrace : WordTrace (prefixWord ++ tailWord_5481576) baseStart_5481576 baseEnd_5481576 := by
    simpa [prefixWord, tailWord_5481576, baseEnd_5481576] using wordTrace_append hprefix tailTrace_5481576
  have hstable : (prefixWord ++ tailWord_5481576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481576).length < 2 ^ (prefixWord ++ tailWord_5481576).sum := by decide
  have hdescent : baseEnd_5481576 < baseStart_5481576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481592 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_5481592 : Nat := 118140960795 + 5481592 * 2 ^ 59
def prefixEnd_5481592 : Nat := 4983230072969 + 3 ^ 40 * 5481592 * 2
def baseEnd_5481592 : Nat := 2814691447840622479790623

theorem tailTrace_5481592 : CollatzResearch.WordTrace tailWord_5481592 prefixEnd_5481592 2814691447840622479790623 := by
  unfold tailWord_5481592
  simp only [CollatzResearch.WordTrace]
  refine ⟨99965042578567920112751515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133286723438090560150335353 99965042578567920112751515)
  ·
    refine ⟨149947563867851880169127273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99965042578567920112751515 149947563867851880169127273)
    ·
      refine ⟨112460672900888910126845455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149947563867851880169127273 112460672900888910126845455)
      ·
        refine ⟨168691009351333365190268183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112460672900888910126845455 168691009351333365190268183)
        ·
          refine ⟨253036514027000047785402275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168691009351333365190268183 253036514027000047785402275)
          ·
            refine ⟨379554771040500071678103413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253036514027000047785402275 379554771040500071678103413)
            ·
              refine ⟨35583259785046881719822195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 379554771040500071678103413 35583259785046881719822195)
              ·
                refine ⟨53374889677570322579733293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35583259785046881719822195 53374889677570322579733293)
                ·
                  refine ⟨20015583629088870967399985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53374889677570322579733293 20015583629088870967399985)
                  ·
                    refine ⟨15011687721816653225549989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20015583629088870967399985 15011687721816653225549989)
                    ·
                      refine ⟨2814691447840622479790623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15011687721816653225549989 2814691447840622479790623)
                      ·
                        rfl

theorem cell23_5481592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_5481592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481592 prefixEnd_5481592 := by exact prefixLift 5481592
  have htrace : WordTrace (prefixWord ++ tailWord_5481592) baseStart_5481592 baseEnd_5481592 := by
    simpa [prefixWord, tailWord_5481592, baseEnd_5481592] using wordTrace_append hprefix tailTrace_5481592
  have hstable : (prefixWord ++ tailWord_5481592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481592).length < 2 ^ (prefixWord ++ tailWord_5481592).sum := by decide
  have hdescent : baseEnd_5481592 < baseStart_5481592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481596 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_5481596 : Nat := 118140960795 + 5481596 * 2 ^ 59
def prefixEnd_5481596 : Nat := 4983230072969 + 3 ^ 40 * 5481596 * 2
def baseEnd_5481596 : Nat := 2814693501763240464140605

theorem tailTrace_5481596 : CollatzResearch.WordTrace tailWord_5481596 prefixEnd_5481596 2814693501763240464140605 := by
  unfold tailWord_5481596
  simp only [CollatzResearch.WordTrace]
  refine ⟨99965115524560674454324321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133286820699414232605765761 99965115524560674454324321)
  ·
    refine ⟨74973836643420505840743241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99965115524560674454324321 74973836643420505840743241)
    ·
      refine ⟨56230377482565379380557431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74973836643420505840743241 56230377482565379380557431)
      ·
        refine ⟨84345566223848069070836147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56230377482565379380557431 84345566223848069070836147)
        ·
          refine ⟨126518349335772103606254221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84345566223848069070836147 126518349335772103606254221)
          ·
            refine ⟨47444381000914538852345333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126518349335772103606254221 47444381000914538852345333)
            ·
              refine ⟨4447910718835738017407375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47444381000914538852345333 4447910718835738017407375)
              ·
                refine ⟨6671866078253607026111063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447910718835738017407375 6671866078253607026111063)
                ·
                  refine ⟨10007799117380410539166595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6671866078253607026111063 10007799117380410539166595)
                  ·
                    refine ⟨15011698676070615808749893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10007799117380410539166595 15011698676070615808749893)
                    ·
                      refine ⟨2814693501763240464140605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15011698676070615808749893 2814693501763240464140605)
                      ·
                        rfl

theorem cell23_5481596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_5481596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481596 prefixEnd_5481596 := by exact prefixLift 5481596
  have htrace : WordTrace (prefixWord ++ tailWord_5481596) baseStart_5481596 baseEnd_5481596 := by
    simpa [prefixWord, tailWord_5481596, baseEnd_5481596] using wordTrace_append hprefix tailTrace_5481596
  have hstable : (prefixWord ++ tailWord_5481596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481596).length < 2 ^ (prefixWord ++ tailWord_5481596).sum := by decide
  have hdescent : baseEnd_5481596 < baseStart_5481596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481626 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5481626 : Nat := 118140960795 + 5481626 * 2 ^ 59
def prefixEnd_5481626 : Nat := 4983230072969 + 3 ^ 40 * 5481626 * 2
def baseEnd_5481626 : Nat := 2814708906182875346765467

theorem tailTrace_5481626 : CollatzResearch.WordTrace tailWord_5481626 prefixEnd_5481626 2814708906182875346765467 := by
  unfold tailWord_5481626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49982831309753166008060183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133287550159341776021493821 49982831309753166008060183)
  ·
    refine ⟨74974246964629749012090275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49982831309753166008060183 74974246964629749012090275)
    ·
      refine ⟨112461370446944623518135413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74974246964629749012090275 112461370446944623518135413)
      ·
        refine ⟨10543253479401058454825195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112461370446944623518135413 10543253479401058454825195)
        ·
          refine ⟨15814880219101587682237793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543253479401058454825195 15814880219101587682237793)
          ·
            refine ⟨11861160164326190761678345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15814880219101587682237793 11861160164326190761678345)
            ·
              refine ⟨8895870123244643071258759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11861160164326190761678345 8895870123244643071258759)
              ·
                refine ⟨13343805184866964606888139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895870123244643071258759 13343805184866964606888139)
                ·
                  refine ⟨20015707777300446910332209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13343805184866964606888139 20015707777300446910332209)
                  ·
                    refine ⟨15011780832975335182749157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20015707777300446910332209 15011780832975335182749157)
                    ·
                      refine ⟨2814708906182875346765467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15011780832975335182749157 2814708906182875346765467)
                      ·
                        rfl

theorem cell23_5481626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5481626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481626 prefixEnd_5481626 := by exact prefixLift 5481626
  have htrace : WordTrace (prefixWord ++ tailWord_5481626) baseStart_5481626 baseEnd_5481626 := by
    simpa [prefixWord, tailWord_5481626, baseEnd_5481626] using wordTrace_append hprefix tailTrace_5481626
  have hstable : (prefixWord ++ tailWord_5481626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481626).length < 2 ^ (prefixWord ++ tailWord_5481626).sum := by decide
  have hdescent : baseEnd_5481626 < baseStart_5481626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481630 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_5481630 : Nat := 118140960795 + 5481630 * 2 ^ 59
def prefixEnd_5481630 : Nat := 4983230072969 + 3 ^ 40 * 5481630 * 2
def baseEnd_5481630 : Nat := 2814710960105493331115449

theorem tailTrace_5481630 : CollatzResearch.WordTrace tailWord_5481630 prefixEnd_5481630 2814710960105493331115449 := by
  unfold tailWord_5481630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24991433891374771589423293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133287647420665448476924229 24991433891374771589423293)
  ·
    refine ⟨9371787709265539346033735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24991433891374771589423293 9371787709265539346033735)
    ·
      refine ⟨14057681563898309019050603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9371787709265539346033735 14057681563898309019050603)
      ·
        refine ⟨21086522345847463528575905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14057681563898309019050603 21086522345847463528575905)
        ·
          refine ⟨15814891759385597646431929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21086522345847463528575905 15814891759385597646431929)
          ·
            refine ⟨11861168819539198234823947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15814891759385597646431929 11861168819539198234823947)
            ·
              refine ⟨17791753229308797352235921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11861168819539198234823947 17791753229308797352235921)
              ·
                refine ⟨13343814921981598014176941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17791753229308797352235921 13343814921981598014176941)
                ·
                  refine ⟨5003930595743099255316353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13343814921981598014176941 5003930595743099255316353)
                  ·
                    refine ⟨3752947946807324441487265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5003930595743099255316353 3752947946807324441487265)
                    ·
                      refine ⟨2814710960105493331115449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3752947946807324441487265 2814710960105493331115449)
                      ·
                        rfl

theorem cell23_5481630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_5481630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481630 prefixEnd_5481630 := by exact prefixLift 5481630
  have htrace : WordTrace (prefixWord ++ tailWord_5481630) baseStart_5481630 baseEnd_5481630 := by
    simpa [prefixWord, tailWord_5481630, baseEnd_5481630] using wordTrace_append hprefix tailTrace_5481630
  have hstable : (prefixWord ++ tailWord_5481630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481630).length < 2 ^ (prefixWord ++ tailWord_5481630).sum := by decide
  have hdescent : baseEnd_5481630 < baseStart_5481630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481632 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 2, 7]
def baseStart_5481632 : Nat := 118140960795 + 5481632 * 2 ^ 59
def prefixEnd_5481632 : Nat := 4983230072969 + 3 ^ 40 * 5481632 * 2
def baseEnd_5481632 : Nat := 938237329022267441096813

theorem tailTrace_5481632 : CollatzResearch.WordTrace tailWord_5481632 prefixEnd_5481632 938237329022267441096813 := by
  unfold tailWord_5481632
  simp only [CollatzResearch.WordTrace]
  refine ⟨99965772038495463528479575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133287696051327284704639433 99965772038495463528479575)
  ·
    refine ⟨149948658057743195292719363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99965772038495463528479575 149948658057743195292719363)
    ·
      refine ⟨224922987086614792939079045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149948658057743195292719363 224922987086614792939079045)
      ·
        refine ⟨42173060078740273676077321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224922987086614792939079045 42173060078740273676077321)
        ·
          refine ⟨31629795059055205257057991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42173060078740273676077321 31629795059055205257057991)
          ·
            refine ⟨47444692588582807885586987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31629795059055205257057991 47444692588582807885586987)
            ·
              refine ⟨71167038882874211828380481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47444692588582807885586987 71167038882874211828380481)
              ·
                refine ⟨53375279162155658871285361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71167038882874211828380481 53375279162155658871285361)
                ·
                  refine ⟨40031459371616744153464021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53375279162155658871285361 40031459371616744153464021)
                  ·
                    refine ⟨938237329022267441096813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40031459371616744153464021 938237329022267441096813)
                    ·
                      rfl

theorem cell23_5481632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_5481632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481632 prefixEnd_5481632 := by exact prefixLift 5481632
  have htrace : WordTrace (prefixWord ++ tailWord_5481632) baseStart_5481632 baseEnd_5481632 := by
    simpa [prefixWord, tailWord_5481632, baseEnd_5481632] using wordTrace_append hprefix tailTrace_5481632
  have hstable : (prefixWord ++ tailWord_5481632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481632).length < 2 ^ (prefixWord ++ tailWord_5481632).sum := by decide
  have hdescent : baseEnd_5481632 < baseStart_5481632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481677 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5481677 : Nat := 118140960795 + 5481677 * 2 ^ 59
def prefixEnd_5481677 : Nat := 4983230072969 + 3 ^ 40 * 5481677 * 2
def baseEnd_5481677 : Nat := 2814735093696254647227733

theorem tailTrace_5481677 : CollatzResearch.WordTrace tailWord_5481677 prefixEnd_5481677 2814735093696254647227733 := by
  unfold tailWord_5481677
  simp only [CollatzResearch.WordTrace]
  refine ⟨199933185361827899742347285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133288790241218599828231523 199933185361827899742347285)
  ·
    refine ⟨9371868063835682800422529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 199933185361827899742347285 9371868063835682800422529)
    ·
      refine ⟨7028901047876762100316897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9371868063835682800422529 7028901047876762100316897)
      ·
        refine ⟨5271675785907571575237673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7028901047876762100316897 5271675785907571575237673)
        ·
          refine ⟨3953756839430678681428255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5271675785907571575237673 3953756839430678681428255)
          ·
            refine ⟨5930635259146018022142383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3953756839430678681428255 5930635259146018022142383)
            ·
              refine ⟨8895952888719027033213575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930635259146018022142383 8895952888719027033213575)
              ·
                refine ⟨13343929333078540549820363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8895952888719027033213575 13343929333078540549820363)
                ·
                  refine ⟨20015893999617810824730545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13343929333078540549820363 20015893999617810824730545)
                  ·
                    refine ⟨15011920499713358118547909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20015893999617810824730545 15011920499713358118547909)
                    ·
                      refine ⟨2814735093696254647227733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15011920499713358118547909 2814735093696254647227733)
                      ·
                        rfl

theorem cell23_5481677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5481677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481677 prefixEnd_5481677 := by exact prefixLift 5481677
  have htrace : WordTrace (prefixWord ++ tailWord_5481677) baseStart_5481677 baseEnd_5481677 := by
    simpa [prefixWord, tailWord_5481677, baseEnd_5481677] using wordTrace_append hprefix tailTrace_5481677
  have hstable : (prefixWord ++ tailWord_5481677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481677).length < 2 ^ (prefixWord ++ tailWord_5481677).sum := by decide
  have hdescent : baseEnd_5481677 < baseStart_5481677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481712 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_5481712 : Nat := 118140960795 + 5481712 * 2 ^ 59
def prefixEnd_5481712 : Nat := 4983230072969 + 3 ^ 40 * 5481712 * 2
def baseEnd_5481712 : Nat := 2814753065519162010290071

theorem tailTrace_5481712 : CollatzResearch.WordTrace tailWord_5481712 prefixEnd_5481712 2814753065519162010290071 := by
  unfold tailWord_5481712
  simp only [CollatzResearch.WordTrace]
  refine ⟨99967230958350550359935695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133289641277800733813247593 99967230958350550359935695)
  ·
    refine ⟨149950846437525825539903543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99967230958350550359935695 149950846437525825539903543)
    ·
      refine ⟨224926269656288738309855315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149950846437525825539903543 224926269656288738309855315)
      ·
        refine ⟨337389404484433107464782973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224926269656288738309855315 337389404484433107464782973)
        ·
          refine ⟨126521026681662415299293615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337389404484433107464782973 126521026681662415299293615)
          ·
            refine ⟨189781540022493622948940423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126521026681662415299293615 189781540022493622948940423)
            ·
              refine ⟨284672310033740434423410635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189781540022493622948940423 284672310033740434423410635)
              ·
                refine ⟨427008465050610651635115953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284672310033740434423410635 427008465050610651635115953)
                ·
                  refine ⟨320256348787957988726336965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427008465050610651635115953 320256348787957988726336965)
                  ·
                    refine ⟨60048065397742122886188181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 320256348787957988726336965 60048065397742122886188181)
                    ·
                      refine ⟨2814753065519162010290071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60048065397742122886188181 2814753065519162010290071)
                      ·
                        rfl

theorem cell23_5481712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_5481712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481712 prefixEnd_5481712 := by exact prefixLift 5481712
  have htrace : WordTrace (prefixWord ++ tailWord_5481712) baseStart_5481712 baseEnd_5481712 := by
    simpa [prefixWord, tailWord_5481712, baseEnd_5481712] using wordTrace_append hprefix tailTrace_5481712
  have hstable : (prefixWord ++ tailWord_5481712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481712).length < 2 ^ (prefixWord ++ tailWord_5481712).sum := by decide
  have hdescent : baseEnd_5481712 < baseStart_5481712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481726 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_5481726 : Nat := 118140960795 + 5481726 * 2 ^ 59
def prefixEnd_5481726 : Nat := 4983230072969 + 3 ^ 40 * 5481726 * 2
def baseEnd_5481726 : Nat := 312751139360924995057223

theorem tailTrace_5481726 : CollatzResearch.WordTrace tailWord_5481726 prefixEnd_5481726 312751139360924995057223 := by
  unfold tailWord_5481726
  simp only [CollatzResearch.WordTrace]
  refine ⟨24991871567331297638860129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133289981692433587407254021 24991871567331297638860129)
  ·
    refine ⟨18743903675498473229145097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24991871567331297638860129 18743903675498473229145097)
    ·
      refine ⟨14057927756623854921858823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18743903675498473229145097 14057927756623854921858823)
      ·
        refine ⟨21086891634935782382788235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14057927756623854921858823 21086891634935782382788235)
        ·
          refine ⟨31630337452403673574182353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21086891634935782382788235 31630337452403673574182353)
          ·
            refine ⟨23722753089302755180636765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31630337452403673574182353 23722753089302755180636765)
            ·
              refine ⟨8896032408488533192738787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23722753089302755180636765 8896032408488533192738787)
              ·
                refine ⟨13344048612732799789108181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896032408488533192738787 13344048612732799789108181)
                ·
                  refine ⟨312751139360924995057223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13344048612732799789108181 312751139360924995057223)
                  ·
                    rfl

theorem cell23_5481726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_5481726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481726 prefixEnd_5481726 := by exact prefixLift 5481726
  have htrace : WordTrace (prefixWord ++ tailWord_5481726) baseStart_5481726 baseEnd_5481726 := by
    simpa [prefixWord, tailWord_5481726, baseEnd_5481726] using wordTrace_append hprefix tailTrace_5481726
  have hstable : (prefixWord ++ tailWord_5481726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481726).length < 2 ^ (prefixWord ++ tailWord_5481726).sum := by decide
  have hdescent : baseEnd_5481726 < baseStart_5481726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481773 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5481773 : Nat := 118140960795 + 5481773 * 2 ^ 59
def prefixEnd_5481773 : Nat := 4983230072969 + 3 ^ 40 * 5481773 * 2
def baseEnd_5481773 : Nat := 938261462613028757209097

theorem tailTrace_5481773 : CollatzResearch.WordTrace tailWord_5481773 prefixEnd_5481773 938261462613028757209097 := by
  unfold tailWord_5481773
  simp only [CollatzResearch.WordTrace]
  refine ⟨199936686769480108137841973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133291124512986738758561315 199936686769480108137841973)
  ·
    refine ⟨18744064384638760137922685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199936686769480108137841973 18744064384638760137922685)
    ·
      refine ⟨7029024144239535051721007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18744064384638760137922685 7029024144239535051721007)
      ·
        refine ⟨10543536216359302577581511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029024144239535051721007 10543536216359302577581511)
        ·
          refine ⟨15815304324538953866372267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543536216359302577581511 15815304324538953866372267)
          ·
            refine ⟨23722956486808430799558401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15815304324538953866372267 23722956486808430799558401)
            ·
              refine ⟨17792217365106323099668801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23722956486808430799558401 17792217365106323099668801)
              ·
                refine ⟨13344163023829742324751601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17792217365106323099668801 13344163023829742324751601)
                ·
                  refine ⟨10008122267872306743563701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13344163023829742324751601 10008122267872306743563701)
                  ·
                    refine ⟨938261462613028757209097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10008122267872306743563701 938261462613028757209097)
                    ·
                      rfl

theorem cell23_5481773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5481773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481773 prefixEnd_5481773 := by exact prefixLift 5481773
  have htrace : WordTrace (prefixWord ++ tailWord_5481773) baseStart_5481773 baseEnd_5481773 := by
    simpa [prefixWord, tailWord_5481773, baseEnd_5481773] using wordTrace_append hprefix tailTrace_5481773
  have hstable : (prefixWord ++ tailWord_5481773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481773).length < 2 ^ (prefixWord ++ tailWord_5481773).sum := by decide
  have hdescent : baseEnd_5481773 < baseStart_5481773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481776 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 2, 4, 2]
def baseStart_5481776 : Nat := 118140960795 + 5481776 * 2 ^ 59
def prefixEnd_5481776 : Nat := 4983230072969 + 3 ^ 40 * 5481776 * 2
def baseEnd_5481776 : Nat := 2814785928281049759889777

theorem tailTrace_5481776 : CollatzResearch.WordTrace tailWord_5481776 prefixEnd_5481776 2814785928281049759889777 := by
  unfold tailWord_5481776
  simp only [CollatzResearch.WordTrace]
  refine ⟨99968398094234619825100591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133291197458979493100134121 99968398094234619825100591)
  ·
    refine ⟨149952597141351929737650887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99968398094234619825100591 149952597141351929737650887)
    ·
      refine ⟨224928895712027894606476331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149952597141351929737650887 224928895712027894606476331)
      ·
        refine ⟨337393343568041841909714497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224928895712027894606476331 337393343568041841909714497)
        ·
          refine ⟨253045007676031381432285873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337393343568041841909714497 253045007676031381432285873)
          ·
            refine ⟨189783755757023536074214405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253045007676031381432285873 189783755757023536074214405)
            ·
              refine ⟨35584454204441913013915201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189783755757023536074214405 35584454204441913013915201)
              ·
                refine ⟨26688340653331434760436401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35584454204441913013915201 26688340653331434760436401)
                ·
                  refine ⟨20016255489998576070327301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26688340653331434760436401 20016255489998576070327301)
                  ·
                    refine ⟨3753047904374733013186369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20016255489998576070327301 3753047904374733013186369)
                    ·
                      refine ⟨2814785928281049759889777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753047904374733013186369 2814785928281049759889777)
                      ·
                        rfl

theorem cell23_5481776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 4, 2].length) (baseStart_5481776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481776 prefixEnd_5481776 := by exact prefixLift 5481776
  have htrace : WordTrace (prefixWord ++ tailWord_5481776) baseStart_5481776 baseEnd_5481776 := by
    simpa [prefixWord, tailWord_5481776, baseEnd_5481776] using wordTrace_append hprefix tailTrace_5481776
  have hstable : (prefixWord ++ tailWord_5481776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481776).length < 2 ^ (prefixWord ++ tailWord_5481776).sum := by decide
  have hdescent : baseEnd_5481776 < baseStart_5481776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481786 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_5481786 : Nat := 118140960795 + 5481786 * 2 ^ 59
def prefixEnd_5481786 : Nat := 4983230072969 + 3 ^ 40 * 5481786 * 2
def baseEnd_5481786 : Nat := 938263687695864906921577

theorem tailTrace_5481786 : CollatzResearch.WordTrace tailWord_5481786 prefixEnd_5481786 938263687695864906921577 := by
  unfold tailWord_5481786
  simp only [CollatzResearch.WordTrace]
  refine ⟨49984290229608252839516303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133291440612288674238710141 49984290229608252839516303)
  ·
    refine ⟨74976435344412379259274455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49984290229608252839516303 74976435344412379259274455)
    ·
      refine ⟨112464653016618568888911683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74976435344412379259274455 112464653016618568888911683)
      ·
        refine ⟨168696979524927853333367525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112464653016618568888911683 168696979524927853333367525)
        ·
          refine ⟨31630683660923972500006411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168696979524927853333367525 31630683660923972500006411)
          ·
            refine ⟨47446025491385958750009617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31630683660923972500006411 47446025491385958750009617)
            ·
              refine ⟨35584519118539469062507213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47446025491385958750009617 35584519118539469062507213)
              ·
                refine ⟨13344194669452300898440205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35584519118539469062507213 13344194669452300898440205)
                ·
                  refine ⟨5004073001044612836915077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13344194669452300898440205 5004073001044612836915077)
                  ·
                    refine ⟨938263687695864906921577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004073001044612836915077 938263687695864906921577)
                    ·
                      rfl

theorem cell23_5481786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_5481786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481786 prefixEnd_5481786 := by exact prefixLift 5481786
  have htrace : WordTrace (prefixWord ++ tailWord_5481786) baseStart_5481786 baseEnd_5481786 := by
    simpa [prefixWord, tailWord_5481786, baseEnd_5481786] using wordTrace_append hprefix tailTrace_5481786
  have hstable : (prefixWord ++ tailWord_5481786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481786).length < 2 ^ (prefixWord ++ tailWord_5481786).sum := by decide
  have hdescent : baseEnd_5481786 < baseStart_5481786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481793 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5481793 : Nat := 118140960795 + 5481793 * 2 ^ 59
def prefixEnd_5481793 : Nat := 4983230072969 + 3 ^ 40 * 5481793 * 2
def baseEnd_5481793 : Nat := 2814794657452176193377199

theorem tailTrace_5481793 : CollatzResearch.WordTrace tailWord_5481793 prefixEnd_5481793 2814794657452176193377199 := by
  unfold tailWord_5481793
  simp only [CollatzResearch.WordTrace]
  refine ⟨199937416229407651553570033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133291610819605101035713355 199937416229407651553570033)
  ·
    refine ⟨149953062172055738665177525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199937416229407651553570033 149953062172055738665177525)
    ·
      refine ⟨14058099578630225499860393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149953062172055738665177525 14058099578630225499860393)
      ·
        refine ⟨10543574683972669124895295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14058099578630225499860393 10543574683972669124895295)
        ·
          refine ⟨15815362025959003687342943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543574683972669124895295 15815362025959003687342943)
          ·
            refine ⟨23723043038938505531014415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15815362025959003687342943 23723043038938505531014415)
            ·
              refine ⟨35584564558407758296521623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23723043038938505531014415 35584564558407758296521623)
              ·
                refine ⟨53376846837611637444782435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35584564558407758296521623 53376846837611637444782435)
                ·
                  refine ⟨80065270256417456167173653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53376846837611637444782435 80065270256417456167173653)
                  ·
                    refine ⟨3753059543269568257836265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80065270256417456167173653 3753059543269568257836265)
                    ·
                      refine ⟨2814794657452176193377199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753059543269568257836265 2814794657452176193377199)
                      ·
                        rfl

theorem cell23_5481793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5481793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481793 prefixEnd_5481793 := by exact prefixLift 5481793
  have htrace : WordTrace (prefixWord ++ tailWord_5481793) baseStart_5481793 baseEnd_5481793 := by
    simpa [prefixWord, tailWord_5481793, baseEnd_5481793] using wordTrace_append hprefix tailTrace_5481793
  have hstable : (prefixWord ++ tailWord_5481793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481793).length < 2 ^ (prefixWord ++ tailWord_5481793).sum := by decide
  have hdescent : baseEnd_5481793 < baseStart_5481793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481813 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_5481813 : Nat := 118140960795 + 5481813 * 2 ^ 59
def prefixEnd_5481813 : Nat := 4983230072969 + 3 ^ 40 * 5481813 * 2
def baseEnd_5481813 : Nat := 2814804927065266115127107

theorem tailTrace_5481813 : CollatzResearch.WordTrace tailWord_5481813 prefixEnd_5481813 2814804927065266115127107 := by
  unfold tailWord_5481813
  simp only [CollatzResearch.WordTrace]
  refine ⟨199938145689335194969298093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133292097126223463312865395 199938145689335194969298093)
  ·
    refine ⟨74976804633500698113486785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199938145689335194969298093 74976804633500698113486785)
    ·
      refine ⟨56232603475125523585115089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74976804633500698113486785 56232603475125523585115089)
      ·
        refine ⟨42174452606344142688836317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56232603475125523585115089 42174452606344142688836317)
        ·
          refine ⟨15815419727379053508313619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42174452606344142688836317 15815419727379053508313619)
          ·
            refine ⟨23723129591068580262470429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15815419727379053508313619 23723129591068580262470429)
            ·
              refine ⟨8896173596650717598426411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23723129591068580262470429 8896173596650717598426411)
              ·
                refine ⟨13344260394976076397639617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896173596650717598426411 13344260394976076397639617)
                ·
                  refine ⟨10008195296232057298229713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13344260394976076397639617 10008195296232057298229713)
                  ·
                    refine ⟨7506146472174042973672285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10008195296232057298229713 7506146472174042973672285)
                    ·
                      refine ⟨2814804927065266115127107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7506146472174042973672285 2814804927065266115127107)
                      ·
                        rfl

theorem cell23_5481813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_5481813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481813 prefixEnd_5481813 := by exact prefixLift 5481813
  have htrace : WordTrace (prefixWord ++ tailWord_5481813) baseStart_5481813 baseEnd_5481813 := by
    simpa [prefixWord, tailWord_5481813, baseEnd_5481813] using wordTrace_append hprefix tailTrace_5481813
  have hstable : (prefixWord ++ tailWord_5481813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481813).length < 2 ^ (prefixWord ++ tailWord_5481813).sum := by decide
  have hdescent : baseEnd_5481813 < baseStart_5481813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481863 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 1, 5]
def baseStart_5481863 : Nat := 118140960795 + 5481863 * 2 ^ 59
def prefixEnd_5481863 : Nat := 4983230072969 + 3 ^ 40 * 5481863 * 2
def baseEnd_5481863 : Nat := 938276867032663639833959

theorem tailTrace_5481863 : CollatzResearch.WordTrace tailWord_5481863 prefixEnd_5481863 938276867032663639833959 := by
  unfold tailWord_5481863
  simp only [CollatzResearch.WordTrace]
  refine ⟨199939969339154053508618243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133293312892769369005745495 199939969339154053508618243)
  ·
    refine ⟨299909954008731080262927365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199939969339154053508618243 299909954008731080262927365)
    ·
      refine ⟨56233116376637077549298881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299909954008731080262927365 56233116376637077549298881)
      ·
        refine ⟨42174837282477808161974161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56233116376637077549298881 42174837282477808161974161)
        ·
          refine ⟨31631127961858356121480621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42174837282477808161974161 31631127961858356121480621)
          ·
            refine ⟨11861672985696883545555233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31631127961858356121480621 11861672985696883545555233)
            ·
              refine ⟨8896254739272662659166425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11861672985696883545555233 8896254739272662659166425)
              ·
                refine ⟨6672191054454496994374819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8896254739272662659166425 6672191054454496994374819)
                ·
                  refine ⟨10008286581681745491562229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6672191054454496994374819 10008286581681745491562229)
                  ·
                    refine ⟨938276867032663639833959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10008286581681745491562229 938276867032663639833959)
                    ·
                      rfl

theorem cell23_5481863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_5481863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481863 prefixEnd_5481863 := by exact prefixLift 5481863
  have htrace : WordTrace (prefixWord ++ tailWord_5481863) baseStart_5481863 baseEnd_5481863 := by
    simpa [prefixWord, tailWord_5481863, baseEnd_5481863] using wordTrace_append hprefix tailTrace_5481863
  have hstable : (prefixWord ++ tailWord_5481863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481863).length < 2 ^ (prefixWord ++ tailWord_5481863).sum := by decide
  have hdescent : baseEnd_5481863 < baseStart_5481863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481900 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 3, 2, 2]
def baseStart_5481900 : Nat := 118140960795 + 5481900 * 2 ^ 59
def prefixEnd_5481900 : Nat := 4983230072969 + 3 ^ 40 * 5481900 * 2
def baseEnd_5481900 : Nat := 2814849599882207274739207

theorem tailTrace_5481900 : CollatzResearch.WordTrace tailWord_5481900 prefixEnd_5481900 2814849599882207274739207 := by
  unfold tailWord_5481900
  simp only [CollatzResearch.WordTrace]
  refine ⟨99970659420010004413857577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133294212560013339218476769 99970659420010004413857577)
  ·
    refine ⟨74977994565007503310393183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99970659420010004413857577 74977994565007503310393183)
    ·
      refine ⟨112466991847511254965589775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74977994565007503310393183 112466991847511254965589775)
      ·
        refine ⟨168700487771266882448384663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112466991847511254965589775 168700487771266882448384663)
        ·
          refine ⟨253050731656900323672576995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168700487771266882448384663 253050731656900323672576995)
          ·
            refine ⟨379576097485350485508865493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253050731656900323672576995 379576097485350485508865493)
            ·
              refine ⟨8896314784812902004114035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 379576097485350485508865493 8896314784812902004114035)
              ·
                refine ⟨13344472177219353006171053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896314784812902004114035 13344472177219353006171053)
                ·
                  refine ⟨5004177066457257377314145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13344472177219353006171053 5004177066457257377314145)
                  ·
                    refine ⟨3753132799842943032985609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5004177066457257377314145 3753132799842943032985609)
                    ·
                      refine ⟨2814849599882207274739207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753132799842943032985609 2814849599882207274739207)
                      ·
                        rfl

theorem cell23_5481900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_5481900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481900 prefixEnd_5481900 := by exact prefixLift 5481900
  have htrace : WordTrace (prefixWord ++ tailWord_5481900) baseStart_5481900 baseEnd_5481900 := by
    simpa [prefixWord, tailWord_5481900, baseEnd_5481900] using wordTrace_append hprefix tailTrace_5481900
  have hstable : (prefixWord ++ tailWord_5481900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481900).length < 2 ^ (prefixWord ++ tailWord_5481900).sum := by decide
  have hdescent : baseEnd_5481900 < baseStart_5481900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5481994 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_5481994 : Nat := 118140960795 + 5481994 * 2 ^ 59
def prefixEnd_5481994 : Nat := 4983230072969 + 3 ^ 40 * 5481994 * 2
def baseEnd_5481994 : Nat := 2814897867063729906963775

theorem tailTrace_5481994 : CollatzResearch.WordTrace tailWord_5481994 prefixEnd_5481994 2814897867063729906963775 := by
  unfold tailWord_5481994
  simp only [CollatzResearch.WordTrace]
  refine ⟨49986186825419865720409259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133296498201119641921091357 49986186825419865720409259)
  ·
    refine ⟨74979280238129798580613889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49986186825419865720409259 74979280238129798580613889)
    ·
      refine ⟨56234460178597348935460417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74979280238129798580613889 56234460178597348935460417)
      ·
        refine ⟨42175845133948011701595313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56234460178597348935460417 42175845133948011701595313)
        ·
          refine ⟨31631883850461008776196485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42175845133948011701595313 31631883850461008776196485)
          ·
            refine ⟨5930978221961439145536841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31631883850461008776196485 5930978221961439145536841)
            ·
              refine ⟨4448233666471079359152631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5930978221961439145536841 4448233666471079359152631)
              ·
                refine ⟨6672350499706619038728947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448233666471079359152631 6672350499706619038728947)
                ·
                  refine ⟨10008525749559928558093421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6672350499706619038728947 10008525749559928558093421)
                  ·
                    refine ⟨3753197156084973209285033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10008525749559928558093421 3753197156084973209285033)
                    ·
                      refine ⟨2814897867063729906963775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753197156084973209285033 2814897867063729906963775)
                      ·
                        rfl

theorem cell23_5481994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_5481994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5481994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5481994 prefixEnd_5481994 := by exact prefixLift 5481994
  have htrace : WordTrace (prefixWord ++ tailWord_5481994) baseStart_5481994 baseEnd_5481994 := by
    simpa [prefixWord, tailWord_5481994, baseEnd_5481994] using wordTrace_append hprefix tailTrace_5481994
  have hstable : (prefixWord ++ tailWord_5481994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5481994).length < 2 ^ (prefixWord ++ tailWord_5481994).sum := by decide
  have hdescent : baseEnd_5481994 < baseStart_5481994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5481994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482013 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 7]
def baseStart_5482013 : Nat := 118140960795 + 5482013 * 2 ^ 59
def prefixEnd_5482013 : Nat := 4983230072969 + 3 ^ 40 * 5482013 * 2
def baseEnd_5482013 : Nat := 312767513688462814736243

theorem tailTrace_5482013 : CollatzResearch.WordTrace tailWord_5482013 prefixEnd_5482013 312767513688462814736243 := by
  unfold tailWord_5482013
  simp only [CollatzResearch.WordTrace]
  refine ⟨199945440288610629126578693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133296960192407086084385795 199945440288610629126578693)
  ·
    refine ⟨37489770054114492961233505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199945440288610629126578693 37489770054114492961233505)
    ·
      refine ⟨28117327540585869720925129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37489770054114492961233505 28117327540585869720925129)
      ·
        refine ⟨21087995655439402290693847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28117327540585869720925129 21087995655439402290693847)
        ·
          refine ⟨31631993483159103436040771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21087995655439402290693847 31631993483159103436040771)
          ·
            refine ⟨47447990224738655154061157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31631993483159103436040771 47447990224738655154061157)
            ·
              refine ⟨8896498167138497841386467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47447990224738655154061157 8896498167138497841386467)
              ·
                refine ⟨13344747250707746762079701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896498167138497841386467 13344747250707746762079701)
                ·
                  refine ⟨312767513688462814736243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13344747250707746762079701 312767513688462814736243)
                  ·
                    rfl

theorem cell23_5482013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_5482013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482013 prefixEnd_5482013 := by exact prefixLift 5482013
  have htrace : WordTrace (prefixWord ++ tailWord_5482013) baseStart_5482013 baseEnd_5482013 := by
    simpa [prefixWord, tailWord_5482013, baseEnd_5482013] using wordTrace_append hprefix tailTrace_5482013
  have hstable : (prefixWord ++ tailWord_5482013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482013).length < 2 ^ (prefixWord ++ tailWord_5482013).sum := by decide
  have hdescent : baseEnd_5482013 < baseStart_5482013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482024 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5482024 : Nat := 118140960795 + 5482024 * 2 ^ 59
def prefixEnd_5482024 : Nat := 4983230072969 + 3 ^ 40 * 5482024 * 2
def baseEnd_5482024 : Nat := 2814913271483364789588637

theorem tailTrace_5482024 : CollatzResearch.WordTrace tailWord_5482024 prefixEnd_5482024 2814913271483364789588637 := by
  unfold tailWord_5482024
  simp only [CollatzResearch.WordTrace]
  refine ⟨99972920745785389002614563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133297227661047185336819417 99972920745785389002614563)
  ·
    refine ⟨149959381118678083503921845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99972920745785389002614563 149959381118678083503921845)
    ·
      refine ⟨14058691979876070328492673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149959381118678083503921845 14058691979876070328492673)
      ·
        refine ⟨10544018984907052746369505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14058691979876070328492673 10544018984907052746369505)
        ·
          refine ⟨7908014238680289559777129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10544018984907052746369505 7908014238680289559777129)
          ·
            refine ⟨5931010679010217169832847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7908014238680289559777129 5931010679010217169832847)
            ·
              refine ⟨8896516018515325754749271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5931010679010217169832847 8896516018515325754749271)
              ·
                refine ⟨13344774027772988632123907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896516018515325754749271 13344774027772988632123907)
                ·
                  refine ⟨20017161041659482948185861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13344774027772988632123907 20017161041659482948185861)
                  ·
                    refine ⟨3753217695311153052784849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20017161041659482948185861 3753217695311153052784849)
                    ·
                      refine ⟨2814913271483364789588637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753217695311153052784849 2814913271483364789588637)
                      ·
                        rfl

theorem cell23_5482024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5482024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482024 prefixEnd_5482024 := by exact prefixLift 5482024
  have htrace : WordTrace (prefixWord ++ tailWord_5482024) baseStart_5482024 baseEnd_5482024 := by
    simpa [prefixWord, tailWord_5482024, baseEnd_5482024] using wordTrace_append hprefix tailTrace_5482024
  have hstable : (prefixWord ++ tailWord_5482024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482024).length < 2 ^ (prefixWord ++ tailWord_5482024).sum := by decide
  have hdescent : baseEnd_5482024 < baseStart_5482024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482153 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_5482153 : Nat := 118140960795 + 5482153 * 2 ^ 59
def prefixEnd_5482153 : Nat := 4983230072969 + 3 ^ 40 * 5482153 * 2
def baseEnd_5482153 : Nat := 2814979510487794784875543

theorem tailTrace_5482153 : CollatzResearch.WordTrace tailWord_5482153 prefixEnd_5482153 2814979510487794784875543 := by
  unfold tailWord_5482153
  simp only [CollatzResearch.WordTrace]
  refine ⟨199950546508103433036675113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133300364338735622024450075 199950546508103433036675113)
  ·
    refine ⟨149962909881077574777506335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199950546508103433036675113 149962909881077574777506335)
    ·
      refine ⟨224944364821616362166259503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149962909881077574777506335 224944364821616362166259503)
      ·
        refine ⟨337416547232424543249389255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224944364821616362166259503 337416547232424543249389255)
        ·
          refine ⟨506124820848636814874083883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337416547232424543249389255 506124820848636814874083883)
          ·
            refine ⟨759187231272955222311125825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506124820848636814874083883 759187231272955222311125825)
            ·
              refine ⟨569390423454716416733344369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759187231272955222311125825 569390423454716416733344369)
              ·
                refine ⟨427042817591037312550008277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569390423454716416733344369 427042817591037312550008277)
                ·
                  refine ⟨10008816037289937012890819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 427042817591037312550008277 10008816037289937012890819)
                  ·
                    refine ⟨15013224055934905519336229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10008816037289937012890819 15013224055934905519336229)
                    ·
                      refine ⟨2814979510487794784875543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15013224055934905519336229 2814979510487794784875543)
                      ·
                        rfl

theorem cell23_5482153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_5482153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482153 prefixEnd_5482153 := by exact prefixLift 5482153
  have htrace : WordTrace (prefixWord ++ tailWord_5482153) baseStart_5482153 baseEnd_5482153 := by
    simpa [prefixWord, tailWord_5482153, baseEnd_5482153] using wordTrace_append hprefix tailTrace_5482153
  have hstable : (prefixWord ++ tailWord_5482153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482153).length < 2 ^ (prefixWord ++ tailWord_5482153).sum := by decide
  have hdescent : baseEnd_5482153 < baseStart_5482153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482157 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_5482157 : Nat := 118140960795 + 5482157 * 2 ^ 59
def prefixEnd_5482157 : Nat := 4983230072969 + 3 ^ 40 * 5482157 * 2
def baseEnd_5482157 : Nat := 2814981564410412769225525

theorem tailTrace_5482157 : CollatzResearch.WordTrace tailWord_5482157 prefixEnd_5482157 2814981564410412769225525 := by
  unfold tailWord_5482157
  simp only [CollatzResearch.WordTrace]
  refine ⟨199950692400088941719820725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133300461600059294479880483 199950692400088941719820725)
  ·
    refine ⟨18745377412508338286233193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199950692400088941719820725 18745377412508338286233193)
    ·
      refine ⟨14059033059381253714674895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18745377412508338286233193 14059033059381253714674895)
      ·
        refine ⟨21088549589071880572012343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14059033059381253714674895 21088549589071880572012343)
        ·
          refine ⟨31632824383607820858018515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21088549589071880572012343 31632824383607820858018515)
          ·
            refine ⟨47449236575411731287027773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31632824383607820858018515 47449236575411731287027773)
            ·
              refine ⟨17793463715779399232635415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47449236575411731287027773 17793463715779399232635415)
              ·
                refine ⟨26690195573669098848953123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17793463715779399232635415 26690195573669098848953123)
                ·
                  refine ⟨40035293360503648273429685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26690195573669098848953123 40035293360503648273429685)
                  ·
                    refine ⟨3753308752547217025634033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40035293360503648273429685 3753308752547217025634033)
                    ·
                      refine ⟨2814981564410412769225525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753308752547217025634033 2814981564410412769225525)
                      ·
                        rfl

theorem cell23_5482157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_5482157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482157 prefixEnd_5482157 := by exact prefixLift 5482157
  have htrace : WordTrace (prefixWord ++ tailWord_5482157) baseStart_5482157 baseEnd_5482157 := by
    simpa [prefixWord, tailWord_5482157, baseEnd_5482157] using wordTrace_append hprefix tailTrace_5482157
  have hstable : (prefixWord ++ tailWord_5482157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482157).length < 2 ^ (prefixWord ++ tailWord_5482157).sum := by decide
  have hdescent : baseEnd_5482157 < baseStart_5482157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482163 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 1, 6]
def baseStart_5482163 : Nat := 118140960795 + 5482163 * 2 ^ 59
def prefixEnd_5482163 : Nat := 4983230072969 + 3 ^ 40 * 5482163 * 2
def baseEnd_5482163 : Nat := 938328215098113248583499

theorem tailTrace_5482163 : CollatzResearch.WordTrace tailWord_5482163 prefixEnd_5482163 938328215098113248583499 := by
  unfold tailWord_5482163
  simp only [CollatzResearch.WordTrace]
  refine ⟨199950911238067204744539143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133300607492044803163026095 199950911238067204744539143)
  ·
    refine ⟨299926366857100807116808715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199950911238067204744539143 299926366857100807116808715)
    ·
      refine ⟨449889550285651210675213073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299926366857100807116808715 449889550285651210675213073)
      ·
        refine ⟨337417162714238408006409805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449889550285651210675213073 337417162714238408006409805)
        ·
          refine ⟨126531436017839403002403677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337417162714238408006409805 126531436017839403002403677)
          ·
            refine ⟨47449288506689776125901379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126531436017839403002403677 47449288506689776125901379)
            ·
              refine ⟨71173932760034664188852069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47449288506689776125901379 71173932760034664188852069)
              ·
                refine ⟨13345112392506499535409763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71173932760034664188852069 13345112392506499535409763)
                ·
                  refine ⟨20017668588759749303114645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13345112392506499535409763 20017668588759749303114645)
                  ·
                    refine ⟨938328215098113248583499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20017668588759749303114645 938328215098113248583499)
                    ·
                      rfl

theorem cell23_5482163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 6].length) (baseStart_5482163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482163 prefixEnd_5482163 := by exact prefixLift 5482163
  have htrace : WordTrace (prefixWord ++ tailWord_5482163) baseStart_5482163 baseEnd_5482163 := by
    simpa [prefixWord, tailWord_5482163, baseEnd_5482163] using wordTrace_append hprefix tailTrace_5482163
  have hstable : (prefixWord ++ tailWord_5482163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482163).length < 2 ^ (prefixWord ++ tailWord_5482163).sum := by decide
  have hdescent : baseEnd_5482163 < baseStart_5482163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482167 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 1, 5]
def baseStart_5482167 : Nat := 118140960795 + 5482167 * 2 ^ 59
def prefixEnd_5482167 : Nat := 4983230072969 + 3 ^ 40 * 5482167 * 2
def baseEnd_5482167 : Nat := 938328899738985910033493

theorem tailTrace_5482167 : CollatzResearch.WordTrace tailWord_5482167 prefixEnd_5482167 938328899738985910033493 := by
  unfold tailWord_5482167
  simp only [CollatzResearch.WordTrace]
  refine ⟨199951057130052713427684755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133300704753368475618456503 199951057130052713427684755)
  ·
    refine ⟨299926585695079070141527133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199951057130052713427684755 299926585695079070141527133)
    ·
      refine ⟨112472469635654651303072675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299926585695079070141527133 112472469635654651303072675)
      ·
        refine ⟨168708704453481976954609013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112472469635654651303072675 168708704453481976954609013)
        ·
          refine ⟨15816441042513935339494595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168708704453481976954609013 15816441042513935339494595)
          ·
            refine ⟨23724661563770903009241893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15816441042513935339494595 23724661563770903009241893)
            ·
              refine ⟨4448374043207044314232855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23724661563770903009241893 4448374043207044314232855)
              ·
                refine ⟨6672561064810566471349283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448374043207044314232855 6672561064810566471349283)
                ·
                  refine ⟨10008841597215849707023925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6672561064810566471349283 10008841597215849707023925)
                  ·
                    refine ⟨938328899738985910033493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10008841597215849707023925 938328899738985910033493)
                    ·
                      rfl

theorem cell23_5482167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_5482167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482167 prefixEnd_5482167 := by exact prefixLift 5482167
  have htrace : WordTrace (prefixWord ++ tailWord_5482167) baseStart_5482167 baseEnd_5482167 := by
    simpa [prefixWord, tailWord_5482167, baseEnd_5482167] using wordTrace_append hprefix tailTrace_5482167
  have hstable : (prefixWord ++ tailWord_5482167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482167).length < 2 ^ (prefixWord ++ tailWord_5482167).sum := by decide
  have hdescent : baseEnd_5482167 < baseStart_5482167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482183 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5482183 : Nat := 118140960795 + 5482183 * 2 ^ 59
def prefixEnd_5482183 : Nat := 4983230072969 + 3 ^ 40 * 5482183 * 2
def baseEnd_5482183 : Nat := 2814994914907429667500405

theorem tailTrace_5482183 : CollatzResearch.WordTrace tailWord_5482183 prefixEnd_5482183 2814994914907429667500405 := by
  unfold tailWord_5482183
  simp only [CollatzResearch.WordTrace]
  refine ⟨199951640697994748160267203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133301093798663165440178135 199951640697994748160267203)
  ·
    refine ⟨299927461046992122240400805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199951640697994748160267203 299927461046992122240400805)
    ·
      refine ⟨56236398946311022920075151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299927461046992122240400805 56236398946311022920075151)
      ·
        refine ⟨84354598419466534380112727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56236398946311022920075151 84354598419466534380112727)
        ·
          refine ⟨126531897629199801570169091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84354598419466534380112727 126531897629199801570169091)
          ·
            refine ⟨189797846443799702355253637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126531897629199801570169091 189797846443799702355253637)
            ·
              refine ⟨35587096208212444191610057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189797846443799702355253637 35587096208212444191610057)
              ·
                refine ⟨26690322156159333143707543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35587096208212444191610057 26690322156159333143707543)
                ·
                  refine ⟨40035483234238999715561315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26690322156159333143707543 40035483234238999715561315)
                  ·
                    refine ⟨60053224851358499573341973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40035483234238999715561315 60053224851358499573341973)
                    ·
                      refine ⟨2814994914907429667500405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60053224851358499573341973 2814994914907429667500405)
                      ·
                        rfl

theorem cell23_5482183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5482183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482183 prefixEnd_5482183 := by exact prefixLift 5482183
  have htrace : WordTrace (prefixWord ++ tailWord_5482183) baseStart_5482183 baseEnd_5482183 := by
    simpa [prefixWord, tailWord_5482183, baseEnd_5482183] using wordTrace_append hprefix tailTrace_5482183
  have hstable : (prefixWord ++ tailWord_5482183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482183).length < 2 ^ (prefixWord ++ tailWord_5482183).sum := by decide
  have hdescent : baseEnd_5482183 < baseStart_5482183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482190 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_5482190 : Nat := 118140960795 + 5482190 * 2 ^ 59
def prefixEnd_5482190 : Nat := 4983230072969 + 3 ^ 40 * 5482190 * 2
def baseEnd_5482190 : Nat := 2814998509272011140112873

theorem tailTrace_5482190 : CollatzResearch.WordTrace tailWord_5482190 prefixEnd_5482190 2814998509272011140112873 := by
  unfold tailWord_5482190
  simp only [CollatzResearch.WordTrace]
  refine ⟨24993987001121173544471503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133301264005979592237181349 24993987001121173544471503)
  ·
    refine ⟨37490980501681760316707255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24993987001121173544471503 37490980501681760316707255)
    ·
      refine ⟨56236470752522640475060883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37490980501681760316707255 56236470752522640475060883)
      ·
        refine ⟨84354706128783960712591325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56236470752522640475060883 84354706128783960712591325)
        ·
          refine ⟨31633014798293985267221747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84354706128783960712591325 31633014798293985267221747)
          ·
            refine ⟨47449522197440977900832621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31633014798293985267221747 47449522197440977900832621)
            ·
              refine ⟨17793570824040366712812233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47449522197440977900832621 17793570824040366712812233)
              ·
                refine ⟨13345178118030275034609175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17793570824040366712812233 13345178118030275034609175)
                ·
                  refine ⟨20017767177045412551913763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13345178118030275034609175 20017767177045412551913763)
                  ·
                    refine ⟨30026650765568118827870645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20017767177045412551913763 30026650765568118827870645)
                    ·
                      refine ⟨2814998509272011140112873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30026650765568118827870645 2814998509272011140112873)
                      ·
                        rfl

theorem cell23_5482190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_5482190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482190 prefixEnd_5482190 := by exact prefixLift 5482190
  have htrace : WordTrace (prefixWord ++ tailWord_5482190) baseStart_5482190 baseEnd_5482190 := by
    simpa [prefixWord, tailWord_5482190, baseEnd_5482190] using wordTrace_append hprefix tailTrace_5482190
  have hstable : (prefixWord ++ tailWord_5482190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482190).length < 2 ^ (prefixWord ++ tailWord_5482190).sum := by decide
  have hdescent : baseEnd_5482190 < baseStart_5482190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482207 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 3]
def baseStart_5482207 : Nat := 118140960795 + 5482207 * 2 ^ 59
def prefixEnd_5482207 : Nat := 4983230072969 + 3 ^ 40 * 5482207 * 2
def baseEnd_5482207 : Nat := 2815007238443137573600295

theorem tailTrace_5482207 : CollatzResearch.WordTrace tailWord_5482207 prefixEnd_5482207 2815007238443137573600295 := by
  unfold tailWord_5482207
  simp only [CollatzResearch.WordTrace]
  refine ⟨199952516049907800259140875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133301677366605200172760583 199952516049907800259140875)
  ·
    refine ⟨299928774074861700388711313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199952516049907800259140875 299928774074861700388711313)
    ·
      refine ⟨224946580556146275291533485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299928774074861700388711313 224946580556146275291533485)
      ·
        refine ⟨84354967708554853234325057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224946580556146275291533485 84354967708554853234325057)
        ·
          refine ⟨63266225781416139925743793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84354967708554853234325057 63266225781416139925743793)
          ·
            refine ⟨47449669336062104944307845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63266225781416139925743793 47449669336062104944307845)
            ·
              refine ⟨8896813000511644677057721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47449669336062104944307845 8896813000511644677057721)
              ·
                refine ⟨6672609750383733507793291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8896813000511644677057721 6672609750383733507793291)
                ·
                  refine ⟨10008914625575600261689937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6672609750383733507793291 10008914625575600261689937)
                  ·
                    refine ⟨7506685969181700196267453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10008914625575600261689937 7506685969181700196267453)
                    ·
                      refine ⟨2815007238443137573600295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7506685969181700196267453 2815007238443137573600295)
                      ·
                        rfl

theorem cell23_5482207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_5482207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482207 prefixEnd_5482207 := by exact prefixLift 5482207
  have htrace : WordTrace (prefixWord ++ tailWord_5482207) baseStart_5482207 baseEnd_5482207 := by
    simpa [prefixWord, tailWord_5482207, baseEnd_5482207] using wordTrace_append hprefix tailTrace_5482207
  have hstable : (prefixWord ++ tailWord_5482207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482207).length < 2 ^ (prefixWord ++ tailWord_5482207).sum := by decide
  have hdescent : baseEnd_5482207 < baseStart_5482207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482215 : List Nat := [1, 1, 5, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5482215 : Nat := 118140960795 + 5482215 * 2 ^ 59
def prefixEnd_5482215 : Nat := 4983230072969 + 3 ^ 40 * 5482215 * 2
def baseEnd_5482215 : Nat := 2815011346288373542300259

theorem tailTrace_5482215 : CollatzResearch.WordTrace tailWord_5482215 prefixEnd_5482215 2815011346288373542300259 := by
  unfold tailWord_5482215
  simp only [CollatzResearch.WordTrace]
  refine ⟨199952807833878817625432099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133301871889252545083621399 199952807833878817625432099)
  ·
    refine ⟨299929211750818226438148149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199952807833878817625432099 299929211750818226438148149)
    ·
      refine ⟨28118363601639208728576389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 299929211750818226438148149 28118363601639208728576389)
      ·
        refine ⟨5272193175307351636608073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28118363601639208728576389 5272193175307351636608073)
        ·
          refine ⟨3954144881480513727456055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5272193175307351636608073 3954144881480513727456055)
          ·
            refine ⟨5931217322220770591184083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954144881480513727456055 5931217322220770591184083)
            ·
              refine ⟨8896825983331155886776125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5931217322220770591184083 8896825983331155886776125)
              ·
                refine ⟨3336309743749183457541047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8896825983331155886776125 3336309743749183457541047)
                ·
                  refine ⟨5004464615623775186311571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336309743749183457541047 5004464615623775186311571)
                  ·
                    refine ⟨7506696923435662779467357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5004464615623775186311571 7506696923435662779467357)
                    ·
                      refine ⟨2815011346288373542300259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7506696923435662779467357 2815011346288373542300259)
                      ·
                        rfl

theorem cell23_5482215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5482215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482215 prefixEnd_5482215 := by exact prefixLift 5482215
  have htrace : WordTrace (prefixWord ++ tailWord_5482215) baseStart_5482215 baseEnd_5482215 := by
    simpa [prefixWord, tailWord_5482215, baseEnd_5482215] using wordTrace_append hprefix tailTrace_5482215
  have hstable : (prefixWord ++ tailWord_5482215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482215).length < 2 ^ (prefixWord ++ tailWord_5482215).sum := by decide
  have hdescent : baseEnd_5482215 < baseStart_5482215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482220 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_5482220 : Nat := 118140960795 + 5482220 * 2 ^ 59
def prefixEnd_5482220 : Nat := 4983230072969 + 3 ^ 40 * 5482220 * 2
def baseEnd_5482220 : Nat := 2815013913691646022737735

theorem tailTrace_5482220 : CollatzResearch.WordTrace tailWord_5482220 prefixEnd_5482220 2815013913691646022737735 := by
  unfold tailWord_5482220
  simp only [CollatzResearch.WordTrace]
  refine ⟨99976495099430351739682057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133301993465907135652909409 99976495099430351739682057)
  ·
    refine ⟨74982371324572763804761543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99976495099430351739682057 74982371324572763804761543)
    ·
      refine ⟨112473556986859145707142315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74982371324572763804761543 112473556986859145707142315)
      ·
        refine ⟨168710335480288718560713473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112473556986859145707142315 168710335480288718560713473)
        ·
          refine ⟨126532751610216538920535105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168710335480288718560713473 126532751610216538920535105)
          ·
            refine ⟨94899563707662404190401329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126532751610216538920535105 94899563707662404190401329)
            ·
              refine ⟨71174672780746803142800997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94899563707662404190401329 71174672780746803142800997)
              ·
                refine ⟨13345251146390025589275187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71174672780746803142800997 13345251146390025589275187)
                ·
                  refine ⟨20017876719585038383912781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13345251146390025589275187 20017876719585038383912781)
                  ·
                    refine ⟨7506703769844389393967293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20017876719585038383912781 7506703769844389393967293)
                    ·
                      refine ⟨2815013913691646022737735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7506703769844389393967293 2815013913691646022737735)
                      ·
                        rfl

theorem cell23_5482220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_5482220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482220 prefixEnd_5482220 := by exact prefixLift 5482220
  have htrace : WordTrace (prefixWord ++ tailWord_5482220) baseStart_5482220 baseEnd_5482220 := by
    simpa [prefixWord, tailWord_5482220, baseEnd_5482220] using wordTrace_append hprefix tailTrace_5482220
  have hstable : (prefixWord ++ tailWord_5482220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482220).length < 2 ^ (prefixWord ++ tailWord_5482220).sum := by decide
  have hdescent : baseEnd_5482220 < baseStart_5482220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482238 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_5482238 : Nat := 118140960795 + 5482238 * 2 ^ 59
def prefixEnd_5482238 : Nat := 4983230072969 + 3 ^ 40 * 5482238 * 2
def baseEnd_5482238 : Nat := 2815023156343426952312653

theorem tailTrace_5482238 : CollatzResearch.WordTrace tailWord_5482238 prefixEnd_5482238 2815023156343426952312653 := by
  unfold tailWord_5482238
  simp only [CollatzResearch.WordTrace]
  refine ⟨24994205839099436569189921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133302431141863661702346245 24994205839099436569189921)
  ·
    refine ⟨18745654379324577426892441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24994205839099436569189921 18745654379324577426892441)
    ·
      refine ⟨14059240784493433070169331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18745654379324577426892441 14059240784493433070169331)
      ·
        refine ⟨21088861176740149605253997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14059240784493433070169331 21088861176740149605253997)
        ·
          refine ⟨7908322941277556101970249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21088861176740149605253997 7908322941277556101970249)
          ·
            refine ⟨5931242205958167076477687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7908322941277556101970249 5931242205958167076477687)
            ·
              refine ⟨8896863308937250614716531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5931242205958167076477687 8896863308937250614716531)
              ·
                refine ⟨13345294963405875922074797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896863308937250614716531 13345294963405875922074797)
                ·
                  refine ⟨5004485611277203470778049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13345294963405875922074797 5004485611277203470778049)
                  ·
                    refine ⟨3753364208457902603083537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5004485611277203470778049 3753364208457902603083537)
                    ·
                      refine ⟨2815023156343426952312653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753364208457902603083537 2815023156343426952312653)
                      ·
                        rfl

theorem cell23_5482238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_5482238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482238 prefixEnd_5482238 := by exact prefixLift 5482238
  have htrace : WordTrace (prefixWord ++ tailWord_5482238) baseStart_5482238 baseEnd_5482238 := by
    simpa [prefixWord, tailWord_5482238, baseEnd_5482238] using wordTrace_append hprefix tailTrace_5482238
  have hstable : (prefixWord ++ tailWord_5482238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482238).length < 2 ^ (prefixWord ++ tailWord_5482238).sum := by decide
  have hdescent : baseEnd_5482238 < baseStart_5482238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482264 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 1, 3, 2]
def baseStart_5482264 : Nat := 118140960795 + 5482264 * 2 ^ 59
def prefixEnd_5482264 : Nat := 4983230072969 + 3 ^ 40 * 5482264 * 2
def baseEnd_5482264 : Nat := 2815036506840443850587533

theorem tailTrace_5482264 : CollatzResearch.WordTrace tailWord_5482264 prefixEnd_5482264 2815036506840443850587533 := by
  unfold tailWord_5482264
  simp only [CollatzResearch.WordTrace]
  refine ⟨99977297505350649496982923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133303063340467532662643897 99977297505350649496982923)
  ·
    refine ⟨149965946258025974245474385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99977297505350649496982923 149965946258025974245474385)
    ·
      refine ⟨112474459693519480684105789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149965946258025974245474385 112474459693519480684105789)
      ·
        refine ⟨42177922385069805256539671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112474459693519480684105789 42177922385069805256539671)
        ·
          refine ⟨63266883577604707884809507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42177922385069805256539671 63266883577604707884809507)
          ·
            refine ⟨94900325366407061827214261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63266883577604707884809507 94900325366407061827214261)
            ·
              refine ⟨8896905503100662046301337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94900325366407061827214261 8896905503100662046301337)
              ·
                refine ⟨6672679127325496534726003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8896905503100662046301337 6672679127325496534726003)
                ·
                  refine ⟨10009018690988244802089005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6672679127325496534726003 10009018690988244802089005)
                  ·
                    refine ⟨3753382009120591800783377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10009018690988244802089005 3753382009120591800783377)
                    ·
                      refine ⟨2815036506840443850587533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753382009120591800783377 2815036506840443850587533)
                      ·
                        rfl

theorem cell23_5482264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_5482264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482264 prefixEnd_5482264 := by exact prefixLift 5482264
  have htrace : WordTrace (prefixWord ++ tailWord_5482264) baseStart_5482264 baseEnd_5482264 := by
    simpa [prefixWord, tailWord_5482264, baseEnd_5482264] using wordTrace_append hprefix tailTrace_5482264
  have hstable : (prefixWord ++ tailWord_5482264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482264).length < 2 ^ (prefixWord ++ tailWord_5482264).sum := by decide
  have hdescent : baseEnd_5482264 < baseStart_5482264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482277 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 3, 4, 2]
def baseStart_5482277 : Nat := 118140960795 + 5482277 * 2 ^ 59
def prefixEnd_5482277 : Nat := 4983230072969 + 3 ^ 40 * 5482277 * 2
def baseEnd_5482277 : Nat := 2815043182088952299724973

theorem tailTrace_5482277 : CollatzResearch.WordTrace tailWord_5482277 prefixEnd_5482277 2815043182088952299724973 := by
  unfold tailWord_5482277
  simp only [CollatzResearch.WordTrace]
  refine ⟨199955069159654202214189085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133303379439769468142792723 199955069159654202214189085)
  ·
    refine ⟨74983150934870325830320907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199955069159654202214189085 74983150934870325830320907)
    ·
      refine ⟨112474726402305488745481361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74983150934870325830320907 112474726402305488745481361)
      ·
        refine ⟨84356044801729116559111021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112474726402305488745481361 84356044801729116559111021)
        ·
          refine ⟨31633516800648418709666633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84356044801729116559111021 31633516800648418709666633)
          ·
            refine ⟨23725137600486314032249975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31633516800648418709666633 23725137600486314032249975)
            ·
              refine ⟨35587706400729471048374963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23725137600486314032249975 35587706400729471048374963)
              ·
                refine ⟨53381559601094206572562445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35587706400729471048374963 53381559601094206572562445)
                ·
                  refine ⟨20018084850410327464710917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53381559601094206572562445 20018084850410327464710917)
                  ·
                    refine ⟨3753390909451936399633297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20018084850410327464710917 3753390909451936399633297)
                    ·
                      refine ⟨2815043182088952299724973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753390909451936399633297 2815043182088952299724973)
                      ·
                        rfl

theorem cell23_5482277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_5482277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482277 prefixEnd_5482277 := by exact prefixLift 5482277
  have htrace : WordTrace (prefixWord ++ tailWord_5482277) baseStart_5482277 baseEnd_5482277 := by
    simpa [prefixWord, tailWord_5482277, baseEnd_5482277] using wordTrace_append hprefix tailTrace_5482277
  have hstable : (prefixWord ++ tailWord_5482277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482277).length < 2 ^ (prefixWord ++ tailWord_5482277).sum := by decide
  have hdescent : baseEnd_5482277 < baseStart_5482277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482317 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 9]
def baseStart_5482317 : Nat := 118140960795 + 5482317 * 2 ^ 59
def prefixEnd_5482317 : Nat := 4983230072969 + 3 ^ 40 * 5482317 * 2
def baseEnd_5482317 : Nat := 312784857923903571469421

theorem tailTrace_5482317 : CollatzResearch.WordTrace tailWord_5482317 prefixEnd_5482317 312784857923903571469421 := by
  unfold tailWord_5482317
  simp only [CollatzResearch.WordTrace]
  refine ⟨199956528079509289045645205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133304352053006192697096803 199956528079509289045645205)
  ·
    refine ⟨9372962253726997924014619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 199956528079509289045645205 9372962253726997924014619)
    ·
      refine ⟨14059443380590496886021929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9372962253726997924014619 14059443380590496886021929)
      ·
        refine ⟨10544582535442872664516447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14059443380590496886021929 10544582535442872664516447)
        ·
          refine ⟨15816873803164308996774671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544582535442872664516447 15816873803164308996774671)
          ·
            refine ⟨23725310704746463495162007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15816873803164308996774671 23725310704746463495162007)
            ·
              refine ⟨35587966057119695242743011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23725310704746463495162007 35587966057119695242743011)
              ·
                refine ⟨53381949085679542864114517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35587966057119695242743011 53381949085679542864114517)
                ·
                  refine ⟨312784857923903571469421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53381949085679542864114517 312784857923903571469421)
                  ·
                    rfl

theorem cell23_5482317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_5482317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482317 prefixEnd_5482317 := by exact prefixLift 5482317
  have htrace : WordTrace (prefixWord ++ tailWord_5482317) baseStart_5482317 baseEnd_5482317 := by
    simpa [prefixWord, tailWord_5482317, baseEnd_5482317] using wordTrace_append hprefix tailTrace_5482317
  have hstable : (prefixWord ++ tailWord_5482317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482317).length < 2 ^ (prefixWord ++ tailWord_5482317).sum := by decide
  have hdescent : baseEnd_5482317 < baseStart_5482317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482330 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_5482330 : Nat := 118140960795 + 5482330 * 2 ^ 59
def prefixEnd_5482330 : Nat := 4983230072969 + 3 ^ 40 * 5482330 * 2
def baseEnd_5482330 : Nat := 938356798854546864120743

theorem tailTrace_5482330 : CollatzResearch.WordTrace tailWord_5482330 prefixEnd_5482330 938356798854546864120743 := by
  unfold tailWord_5482330
  simp only [CollatzResearch.WordTrace]
  refine ⟨49989250557115548066467111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133304668152308128177245629 49989250557115548066467111)
  ·
    refine ⟨74983875835673322099700667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49989250557115548066467111 74983875835673322099700667)
    ·
      refine ⟨112475813753509983149551001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74983875835673322099700667 112475813753509983149551001)
      ·
        refine ⟨84356860315132487362163251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112475813753509983149551001 84356860315132487362163251)
        ·
          refine ⟨126535290472698731043244877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84356860315132487362163251 126535290472698731043244877)
          ·
            refine ⟨47450733927262024141216829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126535290472698731043244877 47450733927262024141216829)
            ·
              refine ⟨17794025222723259052956311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47450733927262024141216829 17794025222723259052956311)
              ·
                refine ⟨26691037834084888579434467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17794025222723259052956311 26691037834084888579434467)
                ·
                  refine ⟨40036556751127332869151701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26691037834084888579434467 40036556751127332869151701)
                  ·
                    refine ⟨938356798854546864120743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40036556751127332869151701 938356798854546864120743)
                    ·
                      rfl

theorem cell23_5482330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_5482330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482330 prefixEnd_5482330 := by exact prefixLift 5482330
  have htrace : WordTrace (prefixWord ++ tailWord_5482330) baseStart_5482330 baseEnd_5482330 := by
    simpa [prefixWord, tailWord_5482330, baseEnd_5482330] using wordTrace_append hprefix tailTrace_5482330
  have hstable : (prefixWord ++ tailWord_5482330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482330).length < 2 ^ (prefixWord ++ tailWord_5482330).sum := by decide
  have hdescent : baseEnd_5482330 < baseStart_5482330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482377 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 3, 4]
def baseStart_5482377 : Nat := 118140960795 + 5482377 * 2 ^ 59
def prefixEnd_5482377 : Nat := 4983230072969 + 3 ^ 40 * 5482377 * 2
def baseEnd_5482377 : Nat := 938364843384800636158171

theorem tailTrace_5482377 : CollatzResearch.WordTrace tailWord_5482377 prefixEnd_5482377 938364843384800636158171 := by
  unfold tailWord_5482377
  simp only [CollatzResearch.WordTrace]
  refine ⟨199958716459291919292829385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133305810972861279528552923 199958716459291919292829385)
  ·
    refine ⟨149969037344468939469622039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199958716459291919292829385 149969037344468939469622039)
    ·
      refine ⟨224953556016703409204433059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149969037344468939469622039 224953556016703409204433059)
      ·
        refine ⟨337430334025055113806649589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224953556016703409204433059 337430334025055113806649589)
        ·
          refine ⟨31634093814848916919373399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 337430334025055113806649589 31634093814848916919373399)
          ·
            refine ⟨47451140722273375379060099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31634093814848916919373399 47451140722273375379060099)
            ·
              refine ⟨71176711083410063068590149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47451140722273375379060099 71176711083410063068590149)
              ·
                refine ⟨13345633328139386825360653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71176711083410063068590149 13345633328139386825360653)
                ·
                  refine ⟨5004612498052270059510245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13345633328139386825360653 5004612498052270059510245)
                  ·
                    refine ⟨938364843384800636158171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004612498052270059510245 938364843384800636158171)
                    ·
                      rfl

theorem cell23_5482377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_5482377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482377 prefixEnd_5482377 := by exact prefixLift 5482377
  have htrace : WordTrace (prefixWord ++ tailWord_5482377) baseStart_5482377 baseEnd_5482377 := by
    simpa [prefixWord, tailWord_5482377, baseEnd_5482377] using wordTrace_append hprefix tailTrace_5482377
  have hstable : (prefixWord ++ tailWord_5482377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482377).length < 2 ^ (prefixWord ++ tailWord_5482377).sum := by decide
  have hdescent : baseEnd_5482377 < baseStart_5482377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482380 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_5482380 : Nat := 118140960795 + 5482380 * 2 ^ 59
def prefixEnd_5482380 : Nat := 4983230072969 + 3 ^ 40 * 5482380 * 2
def baseEnd_5482380 : Nat := 2815096070596365396736999

theorem tailTrace_5482380 : CollatzResearch.WordTrace tailWord_5482380 prefixEnd_5482380 2815096070596365396736999 := by
  unfold tailWord_5482380
  simp only [CollatzResearch.WordTrace]
  refine ⟨99979412939140525402594297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133305883918854033870125729 99979412939140525402594297)
  ·
    refine ⟨74984559704355394051945723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99979412939140525402594297 74984559704355394051945723)
    ·
      refine ⟨112476839556533091077918585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74984559704355394051945723 112476839556533091077918585)
      ·
        refine ⟨84357629667399818308438939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112476839556533091077918585 84357629667399818308438939)
        ·
          refine ⟨126536444501099727462658409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84357629667399818308438939 126536444501099727462658409)
          ·
            refine ⟨94902333375824795596993807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126536444501099727462658409 94902333375824795596993807)
            ·
              refine ⟨142353500063737193395490711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94902333375824795596993807 142353500063737193395490711)
              ·
                refine ⟨213530250095605790093236067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142353500063737193395490711 213530250095605790093236067)
                ·
                  refine ⟨320295375143408685139854101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213530250095605790093236067 320295375143408685139854101)
                  ·
                    refine ⟨15013845709847282115930661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 320295375143408685139854101 15013845709847282115930661)
                    ·
                      refine ⟨2815096070596365396736999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15013845709847282115930661 2815096070596365396736999)
                      ·
                        rfl

theorem cell23_5482380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_5482380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482380 prefixEnd_5482380 := by exact prefixLift 5482380
  have htrace : WordTrace (prefixWord ++ tailWord_5482380) baseStart_5482380 baseEnd_5482380 := by
    simpa [prefixWord, tailWord_5482380, baseEnd_5482380] using wordTrace_append hprefix tailTrace_5482380
  have hstable : (prefixWord ++ tailWord_5482380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482380).length < 2 ^ (prefixWord ++ tailWord_5482380).sum := by decide
  have hdescent : baseEnd_5482380 < baseStart_5482380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482404 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_5482404 : Nat := 118140960795 + 5482404 * 2 ^ 59
def prefixEnd_5482404 : Nat := 4983230072969 + 3 ^ 40 * 5482404 * 2
def baseEnd_5482404 : Nat := 2815108394132073302836889

theorem tailTrace_5482404 : CollatzResearch.WordTrace tailWord_5482404 prefixEnd_5482404 2815108394132073302836889 := by
  unfold tailWord_5482404
  simp only [CollatzResearch.WordTrace]
  refine ⟨99979850615097051452031133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133306467486796068602708177 99979850615097051452031133)
  ·
    refine ⟨37492443980661394294511675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99979850615097051452031133 37492443980661394294511675)
    ·
      refine ⟨56238665970992091441767513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37492443980661394294511675 56238665970992091441767513)
      ·
        refine ⟨42178999478244068581325635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56238665970992091441767513 42178999478244068581325635)
        ·
          refine ⟨63268499217366102871988453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42178999478244068581325635 63268499217366102871988453)
          ·
            refine ⟨11862843603256144288497835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63268499217366102871988453 11862843603256144288497835)
            ·
              refine ⟨17794265404884216432746753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11862843603256144288497835 17794265404884216432746753)
              ·
                refine ⟨13345699053663162324560065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17794265404884216432746753 13345699053663162324560065)
                ·
                  refine ⟨10009274290247371743420049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13345699053663162324560065 10009274290247371743420049)
                  ·
                    refine ⟨7506955717685528807565037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10009274290247371743420049 7506955717685528807565037)
                    ·
                      refine ⟨2815108394132073302836889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7506955717685528807565037 2815108394132073302836889)
                      ·
                        rfl

theorem cell23_5482404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_5482404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482404 prefixEnd_5482404 := by exact prefixLift 5482404
  have htrace : WordTrace (prefixWord ++ tailWord_5482404) baseStart_5482404 baseEnd_5482404 := by
    simpa [prefixWord, tailWord_5482404, baseEnd_5482404] using wordTrace_append hprefix tailTrace_5482404
  have hstable : (prefixWord ++ tailWord_5482404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482404).length < 2 ^ (prefixWord ++ tailWord_5482404).sum := by decide
  have hdescent : baseEnd_5482404 < baseStart_5482404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482407 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 8]
def baseStart_5482407 : Nat := 118140960795 + 5482407 * 2 ^ 59
def prefixEnd_5482407 : Nat := 4983230072969 + 3 ^ 40 * 5482407 * 2
def baseEnd_5482407 : Nat := 312789992730448532344375

theorem tailTrace_5482407 : CollatzResearch.WordTrace tailWord_5482407 prefixEnd_5482407 312789992730448532344375 := by
  unfold tailWord_5482407
  simp only [CollatzResearch.WordTrace]
  refine ⟨199959810649183234416421475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133306540432788822944280983 199959810649183234416421475)
  ·
    refine ⟨299939715973774851624632213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199959810649183234416421475 299939715973774851624632213)
    ·
      refine ⟨14059674186270696169904635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299939715973774851624632213 14059674186270696169904635)
      ·
        refine ⟨21089511279406044254856953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14059674186270696169904635 21089511279406044254856953)
        ·
          refine ⟨15817133459554533191142715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21089511279406044254856953 15817133459554533191142715)
          ·
            refine ⟨23725700189331799786714073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15817133459554533191142715 23725700189331799786714073)
            ·
              refine ⟨17794275141998849840035555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23725700189331799786714073 17794275141998849840035555)
              ·
                refine ⟨26691412712998274760053333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17794275141998849840035555 26691412712998274760053333)
                ·
                  refine ⟨312789992730448532344375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26691412712998274760053333 312789992730448532344375)
                  ·
                    rfl

theorem cell23_5482407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 8].length) (baseStart_5482407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482407 prefixEnd_5482407 := by exact prefixLift 5482407
  have htrace : WordTrace (prefixWord ++ tailWord_5482407) baseStart_5482407 baseEnd_5482407 := by
    simpa [prefixWord, tailWord_5482407, baseEnd_5482407] using wordTrace_append hprefix tailTrace_5482407
  have hstable : (prefixWord ++ tailWord_5482407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482407).length < 2 ^ (prefixWord ++ tailWord_5482407).sum := by decide
  have hdescent : baseEnd_5482407 < baseStart_5482407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482437 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_5482437 : Nat := 118140960795 + 5482437 * 2 ^ 59
def prefixEnd_5482437 : Nat := 4983230072969 + 3 ^ 40 * 5482437 * 2
def baseEnd_5482437 : Nat := 938375112997890557908079

theorem tailTrace_5482437 : CollatzResearch.WordTrace tailWord_5482437 prefixEnd_5482437 938375112997890557908079 := by
  unfold tailWord_5482437
  simp only [CollatzResearch.WordTrace]
  refine ⟨199960904839074549540013565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133307269892716366360009043 199960904839074549540013565)
  ·
    refine ⟨74985339314652956077505087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199960904839074549540013565 74985339314652956077505087)
    ·
      refine ⟨112478008971979434116257631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74985339314652956077505087 112478008971979434116257631)
      ·
        refine ⟨168717013457969151174386447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112478008971979434116257631 168717013457969151174386447)
        ·
          refine ⟨253075520186953726761579671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168717013457969151174386447 253075520186953726761579671)
          ·
            refine ⟨379613280280430590142369507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253075520186953726761579671 379613280280430590142369507)
            ·
              refine ⟨569419920420645885213554261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379613280280430590142369507 569419920420645885213554261)
              ·
                refine ⟨6672889692429443967346339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 569419920420645885213554261 6672889692429443967346339)
                ·
                  refine ⟨10009334538644165951019509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6672889692429443967346339 10009334538644165951019509)
                  ·
                    refine ⟨938375112997890557908079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10009334538644165951019509 938375112997890557908079)
                    ·
                      rfl

theorem cell23_5482437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_5482437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482437 prefixEnd_5482437 := by exact prefixLift 5482437
  have htrace : WordTrace (prefixWord ++ tailWord_5482437) baseStart_5482437 baseEnd_5482437 := by
    simpa [prefixWord, tailWord_5482437, baseEnd_5482437] using wordTrace_append hprefix tailTrace_5482437
  have hstable : (prefixWord ++ tailWord_5482437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482437).length < 2 ^ (prefixWord ++ tailWord_5482437).sum := by decide
  have hdescent : baseEnd_5482437 < baseStart_5482437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482525 : List Nat := [1, 4, 2, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_5482525 : Nat := 118140960795 + 5482525 * 2 ^ 59
def prefixEnd_5482525 : Nat := 4983230072969 + 3 ^ 40 * 5482525 * 2
def baseEnd_5482525 : Nat := 2815170525291267329423833

theorem tailTrace_5482525 : CollatzResearch.WordTrace tailWord_5482525 prefixEnd_5482525 2815170525291267329423833 := by
  unfold tailWord_5482525
  simp only [CollatzResearch.WordTrace]
  refine ⟨199964114462755740569217029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133309409641837160379478019 199964114462755740569217029)
  ·
    refine ⟨37493271461766701356728193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199964114462755740569217029 37493271461766701356728193)
    ·
      refine ⟨28119953596325026017546145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37493271461766701356728193 28119953596325026017546145)
      ·
        refine ⟨21089965197243769513159609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28119953596325026017546145 21089965197243769513159609)
        ·
          refine ⟨15817473897932827134869707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21089965197243769513159609 15817473897932827134869707)
          ·
            refine ⟨23726210846899240702304561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15817473897932827134869707 23726210846899240702304561)
            ·
              refine ⟨17794658135174430526728421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23726210846899240702304561 17794658135174430526728421)
              ·
                refine ⟨3336498400345205723761579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17794658135174430526728421 3336498400345205723761579)
                ·
                  refine ⟨5004747600517808585642369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336498400345205723761579 5004747600517808585642369)
                  ·
                    refine ⟨3753560700388356439231777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5004747600517808585642369 3753560700388356439231777)
                    ·
                      refine ⟨2815170525291267329423833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753560700388356439231777 2815170525291267329423833)
                      ·
                        rfl

theorem cell23_5482525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_5482525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482525 prefixEnd_5482525 := by exact prefixLift 5482525
  have htrace : WordTrace (prefixWord ++ tailWord_5482525) baseStart_5482525 baseEnd_5482525 := by
    simpa [prefixWord, tailWord_5482525, baseEnd_5482525] using wordTrace_append hprefix tailTrace_5482525
  have hstable : (prefixWord ++ tailWord_5482525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482525).length < 2 ^ (prefixWord ++ tailWord_5482525).sum := by decide
  have hdescent : baseEnd_5482525 < baseStart_5482525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482535 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5482535 : Nat := 118140960795 + 5482535 * 2 ^ 59
def prefixEnd_5482535 : Nat := 4983230072969 + 3 ^ 40 * 5482535 * 2
def baseEnd_5482535 : Nat := 938391886699270763432929

theorem tailTrace_5482535 : CollatzResearch.WordTrace tailWord_5482535 prefixEnd_5482535 938391886699270763432929 := by
  unfold tailWord_5482535
  simp only [CollatzResearch.WordTrace]
  refine ⟨199964479192719512277081059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133309652795146341518054039 199964479192719512277081059)
  ·
    refine ⟨299946718789079268415621589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199964479192719512277081059 299946718789079268415621589)
    ·
      refine ⟨7030001221619045353491131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 299946718789079268415621589 7030001221619045353491131)
      ·
        refine ⟨10545001832428568030236697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7030001221619045353491131 10545001832428568030236697)
        ·
          refine ⟨7908751374321426022677523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10545001832428568030236697 7908751374321426022677523)
          ·
            refine ⟨11863127061482139034016285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908751374321426022677523 11863127061482139034016285)
            ·
              refine ⟨4448672648055802137756107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11863127061482139034016285 4448672648055802137756107)
              ·
                refine ⟨6673008972083703206634161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4448672648055802137756107 6673008972083703206634161)
                ·
                  refine ⟨5004756729062777404975621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6673008972083703206634161 5004756729062777404975621)
                  ·
                    refine ⟨938391886699270763432929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004756729062777404975621 938391886699270763432929)
                    ·
                      rfl

theorem cell23_5482535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5482535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482535 prefixEnd_5482535 := by exact prefixLift 5482535
  have htrace : WordTrace (prefixWord ++ tailWord_5482535) baseStart_5482535 baseEnd_5482535 := by
    simpa [prefixWord, tailWord_5482535, baseEnd_5482535] using wordTrace_append hprefix tailTrace_5482535
  have hstable : (prefixWord ++ tailWord_5482535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482535).length < 2 ^ (prefixWord ++ tailWord_5482535).sum := by decide
  have hdescent : baseEnd_5482535 < baseStart_5482535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482547 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4]
def baseStart_5482547 : Nat := 118140960795 + 5482547 * 2 ^ 59
def prefixEnd_5482547 : Nat := 4983230072969 + 3 ^ 40 * 5482547 * 2
def baseEnd_5482547 : Nat := 2815181821865666243348731

theorem tailTrace_5482547 : CollatzResearch.WordTrace tailWord_5482547 prefixEnd_5482547 2815181821865666243348731 := by
  unfold tailWord_5482547
  simp only [CollatzResearch.WordTrace]
  refine ⟨199964916868676038326517895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133309944579117358884345263 199964916868676038326517895)
  ·
    refine ⟨299947375303014057489776843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199964916868676038326517895 299947375303014057489776843)
    ·
      refine ⟨449921062954521086234665265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299947375303014057489776843 449921062954521086234665265)
      ·
        refine ⟨337440797215890814675998949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449921062954521086234665265 337440797215890814675998949)
        ·
          refine ⟨63270149477979527751749803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 337440797215890814675998949 63270149477979527751749803)
          ·
            refine ⟨94905224216969291627624705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63270149477979527751749803 94905224216969291627624705)
            ·
              refine ⟨71178918162726968720718529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94905224216969291627624705 71178918162726968720718529)
              ·
                refine ⟨53384188622045226540538897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71178918162726968720718529 53384188622045226540538897)
                ·
                  refine ⟨40038141466533919905404173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53384188622045226540538897 40038141466533919905404173)
                  ·
                    refine ⟨15014303049950219964526565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40038141466533919905404173 15014303049950219964526565)
                    ·
                      refine ⟨2815181821865666243348731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15014303049950219964526565 2815181821865666243348731)
                      ·
                        rfl

theorem cell23_5482547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_5482547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482547 prefixEnd_5482547 := by exact prefixLift 5482547
  have htrace : WordTrace (prefixWord ++ tailWord_5482547) baseStart_5482547 baseEnd_5482547 := by
    simpa [prefixWord, tailWord_5482547, baseEnd_5482547] using wordTrace_append hprefix tailTrace_5482547
  have hstable : (prefixWord ++ tailWord_5482547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482547).length < 2 ^ (prefixWord ++ tailWord_5482547).sum := by decide
  have hdescent : baseEnd_5482547 < baseStart_5482547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482548 : List Nat := [2, 5, 1, 2, 2, 2, 2, 7]
def baseStart_5482548 : Nat := 118140960795 + 5482548 * 2 ^ 59
def prefixEnd_5482548 : Nat := 4983230072969 + 3 ^ 40 * 5482548 * 2
def baseEnd_5482548 : Nat := 104266012420234101460601

theorem tailTrace_5482548 : CollatzResearch.WordTrace tailWord_5482548 prefixEnd_5482548 104266012420234101460601 := by
  unfold tailWord_5482548
  simp only [CollatzResearch.WordTrace]
  refine ⟨99982476670836207748652149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133309968894448276998202865 99982476670836207748652149)
  ·
    refine ⟨9373357187890894476436139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99982476670836207748652149 9373357187890894476436139)
    ·
      refine ⟨14060035781836341714654209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9373357187890894476436139 14060035781836341714654209)
      ·
        refine ⟨10545026836377256285990657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14060035781836341714654209 10545026836377256285990657)
        ·
          refine ⟨7908770127282942214492993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10545026836377256285990657 7908770127282942214492993)
          ·
            refine ⟨5931577595462206660869745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7908770127282942214492993 5931577595462206660869745)
            ·
              refine ⟨4448683196596654995652309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5931577595462206660869745 4448683196596654995652309)
              ·
                refine ⟨104266012420234101460601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4448683196596654995652309 104266012420234101460601)
                ·
                  rfl

theorem cell23_5482548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 7].length) (baseStart_5482548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482548 prefixEnd_5482548 := by exact prefixLift 5482548
  have htrace : WordTrace (prefixWord ++ tailWord_5482548) baseStart_5482548 baseEnd_5482548 := by
    simpa [prefixWord, tailWord_5482548, baseEnd_5482548] using wordTrace_append hprefix tailTrace_5482548
  have hstable : (prefixWord ++ tailWord_5482548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482548).length < 2 ^ (prefixWord ++ tailWord_5482548).sum := by decide
  have hdescent : baseEnd_5482548 < baseStart_5482548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482551 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 1, 3, 2]
def baseStart_5482551 : Nat := 118140960795 + 5482551 * 2 ^ 59
def prefixEnd_5482551 : Nat := 4983230072969 + 3 ^ 40 * 5482551 * 2
def baseEnd_5482551 : Nat := 2815183875788284227698713

theorem tailTrace_5482551 : CollatzResearch.WordTrace tailWord_5482551 prefixEnd_5482551 2815183875788284227698713 := by
  unfold tailWord_5482551
  simp only [CollatzResearch.WordTrace]
  refine ⟨199965062760661547009663507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133310041840441031339775671 199965062760661547009663507)
  ·
    refine ⟨299947594140992320514495261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199965062760661547009663507 299947594140992320514495261)
    ·
      refine ⟨112480347802872120192935723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299947594140992320514495261 112480347802872120192935723)
      ·
        refine ⟨168720521704308180289403585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112480347802872120192935723 168720521704308180289403585)
        ·
          refine ⟨126540391278231135217052689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168720521704308180289403585 126540391278231135217052689)
          ·
            refine ⟨94905293458673351412789517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126540391278231135217052689 94905293458673351412789517)
            ·
              refine ⟨35589485047002506779796069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94905293458673351412789517 35589485047002506779796069)
              ·
                refine ⟨6673028446312970021211763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35589485047002506779796069 6673028446312970021211763)
                ·
                  refine ⟨10009542669469455031817645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6673028446312970021211763 10009542669469455031817645)
                  ·
                    refine ⟨3753578501051045636931617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10009542669469455031817645 3753578501051045636931617)
                    ·
                      refine ⟨2815183875788284227698713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753578501051045636931617 2815183875788284227698713)
                      ·
                        rfl

theorem cell23_5482551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_5482551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482551 prefixEnd_5482551 := by exact prefixLift 5482551
  have htrace : WordTrace (prefixWord ++ tailWord_5482551) baseStart_5482551 baseEnd_5482551 := by
    simpa [prefixWord, tailWord_5482551, baseEnd_5482551] using wordTrace_append hprefix tailTrace_5482551
  have hstable : (prefixWord ++ tailWord_5482551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482551).length < 2 ^ (prefixWord ++ tailWord_5482551).sum := by decide
  have hdescent : baseEnd_5482551 < baseStart_5482551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482602 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_5482602 : Nat := 118140960795 + 5482602 * 2 ^ 59
def prefixEnd_5482602 : Nat := 4983230072969 + 3 ^ 40 * 5482602 * 2
def baseEnd_5482602 : Nat := 2815210063301663528160979

theorem tailTrace_5482602 : CollatzResearch.WordTrace tailWord_5482602 prefixEnd_5482602 2815210063301663528160979 := by
  unfold tailWord_5482602
  simp only [CollatzResearch.WordTrace]
  refine ⟨49991730720869195679942515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133311281922317855146513373 49991730720869195679942515)
  ·
    refine ⟨74987596081303793519913773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49991730720869195679942515 74987596081303793519913773)
    ·
      refine ⟨28120348530488922569967665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74987596081303793519913773 28120348530488922569967665)
      ·
        refine ⟨21090261397866691927475749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28120348530488922569967665 21090261397866691927475749)
        ·
          refine ⟨3954424012100004736401703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21090261397866691927475749 3954424012100004736401703)
          ·
            refine ⟨5931636018150007104602555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954424012100004736401703 5931636018150007104602555)
            ·
              refine ⟨8897454027225010656903833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5931636018150007104602555 8897454027225010656903833)
              ·
                refine ⟨6673090520418757992677875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8897454027225010656903833 6673090520418757992677875)
                ·
                  refine ⟨10009635780628136989016813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6673090520418757992677875 10009635780628136989016813)
                  ·
                    refine ⟨3753613417735551370881305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10009635780628136989016813 3753613417735551370881305)
                    ·
                      refine ⟨2815210063301663528160979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753613417735551370881305 2815210063301663528160979)
                      ·
                        rfl

theorem cell23_5482602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_5482602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482602 prefixEnd_5482602 := by exact prefixLift 5482602
  have htrace : WordTrace (prefixWord ++ tailWord_5482602) baseStart_5482602 baseEnd_5482602 := by
    simpa [prefixWord, tailWord_5482602, baseEnd_5482602] using wordTrace_append hprefix tailTrace_5482602
  have hstable : (prefixWord ++ tailWord_5482602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482602).length < 2 ^ (prefixWord ++ tailWord_5482602).sum := by decide
  have hdescent : baseEnd_5482602 < baseStart_5482602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482638 : List Nat := [4, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_5482638 : Nat := 118140960795 + 5482638 * 2 ^ 59
def prefixEnd_5482638 : Nat := 4983230072969 + 3 ^ 40 * 5482638 * 2
def baseEnd_5482638 : Nat := 312803172067247265256757

theorem tailTrace_5482638 : CollatzResearch.WordTrace tailWord_5482638 prefixEnd_5482638 312803172067247265256757 := by
  unfold tailWord_5482638
  simp only [CollatzResearch.WordTrace]
  refine ⟨24996029488918295108510071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133312157274230907245387045 24996029488918295108510071)
  ·
    refine ⟨37494044233377442662765107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24996029488918295108510071 37494044233377442662765107)
    ·
      refine ⟨56241066350066163994147661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37494044233377442662765107 56241066350066163994147661)
      ·
        refine ⟨21090399881274811497805373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56241066350066163994147661 21090399881274811497805373)
        ·
          refine ⟨7908899955478054311677015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21090399881274811497805373 7908899955478054311677015)
          ·
            refine ⟨11863349933217081467515523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908899955478054311677015 11863349933217081467515523)
            ·
              refine ⟨17795024899825622201273285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11863349933217081467515523 17795024899825622201273285)
              ·
                refine ⟨3336567168717304162738741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17795024899825622201273285 3336567168717304162738741)
                ·
                  refine ⟨312803172067247265256757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3336567168717304162738741 312803172067247265256757)
                  ·
                    rfl

theorem cell23_5482638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_5482638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482638 prefixEnd_5482638 := by exact prefixLift 5482638
  have htrace : WordTrace (prefixWord ++ tailWord_5482638) baseStart_5482638 baseEnd_5482638 := by
    simpa [prefixWord, tailWord_5482638, baseEnd_5482638] using wordTrace_append hprefix tailTrace_5482638
  have hstable : (prefixWord ++ tailWord_5482638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482638).length < 2 ^ (prefixWord ++ tailWord_5482638).sum := by decide
  have hdescent : baseEnd_5482638 < baseStart_5482638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482698 : List Nat := [3, 1, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_5482698 : Nat := 118140960795 + 5482698 * 2 ^ 59
def prefixEnd_5482698 : Nat := 4983230072969 + 3 ^ 40 * 5482698 * 2
def baseEnd_5482698 : Nat := 938419785814831717520179

theorem tailTrace_5482698 : CollatzResearch.WordTrace tailWord_5482698 prefixEnd_5482698 938419785814831717520179 := by
  unfold tailWord_5482698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49992606072782247778816187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133313616194085994076843165 49992606072782247778816187)
  ·
    refine ⟨74988909109173371668224281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49992606072782247778816187 74988909109173371668224281)
    ·
      refine ⟨56241681831880028751168211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74988909109173371668224281 56241681831880028751168211)
      ·
        refine ⟨84362522747820043126752317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56241681831880028751168211 84362522747820043126752317)
        ·
          refine ⟨31635946030432516172532119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84362522747820043126752317 31635946030432516172532119)
          ·
            refine ⟨47453919045648774258798179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31635946030432516172532119 47453919045648774258798179)
            ·
              refine ⟨71180878568473161388197269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47453919045648774258798179 71180878568473161388197269)
              ·
                refine ⟨3336603682897179440071747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71180878568473161388197269 3336603682897179440071747)
                ·
                  refine ⟨5004905524345769160107621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336603682897179440071747 5004905524345769160107621)
                  ·
                    refine ⟨938419785814831717520179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5004905524345769160107621 938419785814831717520179)
                    ·
                      rfl

theorem cell23_5482698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_5482698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482698 prefixEnd_5482698 := by exact prefixLift 5482698
  have htrace : WordTrace (prefixWord ++ tailWord_5482698) baseStart_5482698 baseEnd_5482698 := by
    simpa [prefixWord, tailWord_5482698, baseEnd_5482698] using wordTrace_append hprefix tailTrace_5482698
  have hstable : (prefixWord ++ tailWord_5482698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482698).length < 2 ^ (prefixWord ++ tailWord_5482698).sum := by decide
  have hdescent : baseEnd_5482698 < baseStart_5482698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482731 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 1, 5, 2]
def baseStart_5482731 : Nat := 118140960795 + 5482731 * 2 ^ 59
def prefixEnd_5482731 : Nat := 4983230072969 + 3 ^ 40 * 5482731 * 2
def baseEnd_5482731 : Nat := 2815276302306093523447885

theorem tailTrace_5482731 : CollatzResearch.WordTrace tailWord_5482731 prefixEnd_5482731 2815276302306093523447885 := by
  unfold tailWord_5482731
  simp only [CollatzResearch.WordTrace]
  refine ⟨199971627900009437751216047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133314418600006291834144031 199971627900009437751216047)
  ·
    refine ⟨299957441850014156626824071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199971627900009437751216047 299957441850014156626824071)
    ·
      refine ⟨449936162775021234940236107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299957441850014156626824071 449936162775021234940236107)
      ·
        refine ⟨674904244162531852410354161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449936162775021234940236107 674904244162531852410354161)
        ·
          refine ⟨506178183121898889307765621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674904244162531852410354161 506178183121898889307765621)
          ·
            refine ⟨47454204667678020872603027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 506178183121898889307765621 47454204667678020872603027)
            ·
              refine ⟨71181307001517031308904541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47454204667678020872603027 71181307001517031308904541)
              ·
                refine ⟨26692990125568886740839203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71181307001517031308904541 26692990125568886740839203)
                ·
                  refine ⟨40039485188353330111258805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26692990125568886740839203 40039485188353330111258805)
                  ·
                    refine ⟨3753701736408124697930513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40039485188353330111258805 3753701736408124697930513)
                    ·
                      refine ⟨2815276302306093523447885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753701736408124697930513 2815276302306093523447885)
                      ·
                        rfl

theorem cell23_5482731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5, 2].length) (baseStart_5482731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482731 prefixEnd_5482731 := by exact prefixLift 5482731
  have htrace : WordTrace (prefixWord ++ tailWord_5482731) baseStart_5482731 baseEnd_5482731 := by
    simpa [prefixWord, tailWord_5482731, baseEnd_5482731] using wordTrace_append hprefix tailTrace_5482731
  have hstable : (prefixWord ++ tailWord_5482731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482731).length < 2 ^ (prefixWord ++ tailWord_5482731).sum := by decide
  have hdescent : baseEnd_5482731 < baseStart_5482731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482748 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_5482748 : Nat := 118140960795 + 5482748 * 2 ^ 59
def prefixEnd_5482748 : Nat := 4983230072969 + 3 ^ 40 * 5482748 * 2
def baseEnd_5482748 : Nat := 2815285031477219956935307

theorem tailTrace_5482748 : CollatzResearch.WordTrace tailWord_5482748 prefixEnd_5482748 2815285031477219956935307 := by
  unfold tailWord_5482748
  simp only [CollatzResearch.WordTrace]
  refine ⟨99986123970473924827292449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133314831960631899769723265 99986123970473924827292449)
  ·
    refine ⟨74989592977855443620469337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99986123970473924827292449 74989592977855443620469337)
    ·
      refine ⟨56242194733391582715352003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74989592977855443620469337 56242194733391582715352003)
      ·
        refine ⟨84363292100087374073028005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56242194733391582715352003 84363292100087374073028005)
        ·
          refine ⟨15818117268766382638692751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84363292100087374073028005 15818117268766382638692751)
          ·
            refine ⟨23727175903149573958039127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15818117268766382638692751 23727175903149573958039127)
            ·
              refine ⟨35590763854724360937058691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23727175903149573958039127 35590763854724360937058691)
              ·
                refine ⟨53386145782086541405588037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35590763854724360937058691 53386145782086541405588037)
                ·
                  refine ⟨10009902334141226513547757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53386145782086541405588037 10009902334141226513547757)
                  ·
                    refine ⟨3753713375302959942580409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10009902334141226513547757 3753713375302959942580409)
                    ·
                      refine ⟨2815285031477219956935307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753713375302959942580409 2815285031477219956935307)
                      ·
                        rfl

theorem cell23_5482748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_5482748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482748 prefixEnd_5482748 := by exact prefixLift 5482748
  have htrace : WordTrace (prefixWord ++ tailWord_5482748) baseStart_5482748 baseEnd_5482748 := by
    simpa [prefixWord, tailWord_5482748, baseEnd_5482748] using wordTrace_append hprefix tailTrace_5482748
  have hstable : (prefixWord ++ tailWord_5482748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482748).length < 2 ^ (prefixWord ++ tailWord_5482748).sum := by decide
  have hdescent : baseEnd_5482748 < baseStart_5482748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482778 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_5482778 : Nat := 118140960795 + 5482778 * 2 ^ 59
def prefixEnd_5482778 : Nat := 4983230072969 + 3 ^ 40 * 5482778 * 2
def baseEnd_5482778 : Nat := 2815300435896854839560169

theorem tailTrace_5482778 : CollatzResearch.WordTrace tailWord_5482778 prefixEnd_5482778 2815300435896854839560169 := by
  unfold tailWord_5482778
  simp only [CollatzResearch.WordTrace]
  refine ⟨49993335532709791194544247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133315561420559443185451325 49993335532709791194544247)
  ·
    refine ⟨74990003299064686791816371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49993335532709791194544247 74990003299064686791816371)
    ·
      refine ⟨112485004948597030187724557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74990003299064686791816371 112485004948597030187724557)
      ·
        refine ⟨42181876855723886320396709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112485004948597030187724557 42181876855723886320396709)
        ·
          refine ⟨7909101910448228685074383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42181876855723886320396709 7909101910448228685074383)
          ·
            refine ⟨11863652865672343027611575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7909101910448228685074383 11863652865672343027611575)
            ·
              refine ⟨17795479298508514541417363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11863652865672343027611575 17795479298508514541417363)
              ·
                refine ⟨26693218947762771812126045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17795479298508514541417363 26693218947762771812126045)
                ·
                  refine ⟨10009957105411039429547267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26693218947762771812126045 10009957105411039429547267)
                  ·
                    refine ⟨15014935658116559144320901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10009957105411039429547267 15014935658116559144320901)
                    ·
                      refine ⟨2815300435896854839560169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15014935658116559144320901 2815300435896854839560169)
                      ·
                        rfl

theorem cell23_5482778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_5482778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482778 prefixEnd_5482778 := by exact prefixLift 5482778
  have htrace : WordTrace (prefixWord ++ tailWord_5482778) baseStart_5482778 baseEnd_5482778 := by
    simpa [prefixWord, tailWord_5482778, baseEnd_5482778] using wordTrace_append hprefix tailTrace_5482778
  have hstable : (prefixWord ++ tailWord_5482778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482778).length < 2 ^ (prefixWord ++ tailWord_5482778).sum := by decide
  have hdescent : baseEnd_5482778 < baseStart_5482778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482782 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5482782 : Nat := 118140960795 + 5482782 * 2 ^ 59
def prefixEnd_5482782 : Nat := 4983230072969 + 3 ^ 40 * 5482782 * 2
def baseEnd_5482782 : Nat := 2815302489819472823910151

theorem tailTrace_5482782 : CollatzResearch.WordTrace tailWord_5482782 prefixEnd_5482782 2815302489819472823910151 := by
  unfold tailWord_5482782
  simp only [CollatzResearch.WordTrace]
  refine ⟨24996686002853084182665325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133315658681883115640881733 24996686002853084182665325)
  ·
    refine ⟨9373757251069906568499497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24996686002853084182665325 9373757251069906568499497)
    ·
      refine ⟨7030317938302429926374623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9373757251069906568499497 7030317938302429926374623)
      ·
        refine ⟨10545476907453644889561935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7030317938302429926374623 10545476907453644889561935)
        ·
          refine ⟨15818215361180467334342903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10545476907453644889561935 15818215361180467334342903)
          ·
            refine ⟨23727323041770701001514355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15818215361180467334342903 23727323041770701001514355)
            ·
              refine ⟨35590984562656051502271533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23727323041770701001514355 35590984562656051502271533)
              ·
                refine ⟨13346619210996019313351825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35590984562656051502271533 13346619210996019313351825)
                ·
                  refine ⟨10009964408247014485013869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13346619210996019313351825 10009964408247014485013869)
                  ·
                    refine ⟨3753736653092630431880201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10009964408247014485013869 3753736653092630431880201)
                    ·
                      refine ⟨2815302489819472823910151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753736653092630431880201 2815302489819472823910151)
                      ·
                        rfl

theorem cell23_5482782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5482782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482782 prefixEnd_5482782 := by exact prefixLift 5482782
  have htrace : WordTrace (prefixWord ++ tailWord_5482782) baseStart_5482782 baseEnd_5482782 := by
    simpa [prefixWord, tailWord_5482782, baseEnd_5482782] using wordTrace_append hprefix tailTrace_5482782
  have hstable : (prefixWord ++ tailWord_5482782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482782).length < 2 ^ (prefixWord ++ tailWord_5482782).sum := by decide
  have hdescent : baseEnd_5482782 < baseStart_5482782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482801 : List Nat := [1, 2, 2, 3, 5, 10]
def baseStart_5482801 : Nat := 118140960795 + 5482801 * 2 ^ 59
def prefixEnd_5482801 : Nat := 4983230072969 + 3 ^ 40 * 5482801 * 2
def baseEnd_5482801 : Nat := 11585647102682749998241

theorem tailTrace_5482801 : CollatzResearch.WordTrace tailWord_5482801 prefixEnd_5482801 11585647102682749998241 := by
  unfold tailWord_5482801
  simp only [CollatzResearch.WordTrace]
  refine ⟨199974181009755839706264257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133316120673170559804176171 199974181009755839706264257)
  ·
    refine ⟨149980635757316879779698193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199974181009755839706264257 149980635757316879779698193)
    ·
      refine ⟨112485476817987659834773645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149980635757316879779698193 112485476817987659834773645)
      ·
        refine ⟨42182053806745372438040117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112485476817987659834773645 42182053806745372438040117)
        ·
          refine ⟨3954567544382378666066261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42182053806745372438040117 3954567544382378666066261)
          ·
            refine ⟨11585647102682749998241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3954567544382378666066261 11585647102682749998241)
            ·
              rfl

theorem cell23_5482801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 10].length) (baseStart_5482801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482801 prefixEnd_5482801 := by exact prefixLift 5482801
  have htrace : WordTrace (prefixWord ++ tailWord_5482801) baseStart_5482801 baseEnd_5482801 := by
    simpa [prefixWord, tailWord_5482801, baseEnd_5482801] using wordTrace_append hprefix tailTrace_5482801
  have hstable : (prefixWord ++ tailWord_5482801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482801).length < 2 ^ (prefixWord ++ tailWord_5482801).sum := by decide
  have hdescent : baseEnd_5482801 < baseStart_5482801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482812 : List Nat := [2, 2, 2, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_5482812 : Nat := 118140960795 + 5482812 * 2 ^ 59
def prefixEnd_5482812 : Nat := 4983230072969 + 3 ^ 40 * 5482812 * 2
def baseEnd_5482812 : Nat := 2815317894239107706535013

theorem tailTrace_5482812 : CollatzResearch.WordTrace tailWord_5482812 prefixEnd_5482812 2815317894239107706535013 := by
  unfold tailWord_5482812
  simp only [CollatzResearch.WordTrace]
  refine ⟨99987291106357994292457345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133316388141810659056609793 99987291106357994292457345)
  ·
    refine ⟨74990468329768495719343009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99987291106357994292457345 74990468329768495719343009)
    ·
      refine ⟨56242851247326371789507257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74990468329768495719343009 56242851247326371789507257)
      ·
        refine ⟨42182138435494778842130443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56242851247326371789507257 42182138435494778842130443)
        ·
          refine ⟨63273207653242168263195665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42182138435494778842130443 63273207653242168263195665)
          ·
            refine ⟨47454905739931626197396749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63273207653242168263195665 47454905739931626197396749)
            ·
              refine ⟨17795589652474359824023781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47454905739931626197396749 17795589652474359824023781)
              ·
                refine ⟨3336673059838942467004459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17795589652474359824023781 3336673059838942467004459)
                ·
                  refine ⟨5005009589758413700506689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336673059838942467004459 5005009589758413700506689)
                  ·
                    refine ⟨3753757192318810275380017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5005009589758413700506689 3753757192318810275380017)
                    ·
                      refine ⟨2815317894239107706535013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753757192318810275380017 2815317894239107706535013)
                      ·
                        rfl

theorem cell23_5482812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_5482812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482812 prefixEnd_5482812 := by exact prefixLift 5482812
  have htrace : WordTrace (prefixWord ++ tailWord_5482812) baseStart_5482812 baseEnd_5482812 := by
    simpa [prefixWord, tailWord_5482812, baseEnd_5482812] using wordTrace_append hprefix tailTrace_5482812
  have hstable : (prefixWord ++ tailWord_5482812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482812).length < 2 ^ (prefixWord ++ tailWord_5482812).sum := by decide
  have hdescent : baseEnd_5482812 < baseStart_5482812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482828 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_5482828 : Nat := 118140960795 + 5482828 * 2 ^ 59
def prefixEnd_5482828 : Nat := 4983230072969 + 3 ^ 40 * 5482828 * 2
def baseEnd_5482828 : Nat := 2815326109929579643934939

theorem tailTrace_5482828 : CollatzResearch.WordTrace tailWord_5482828 prefixEnd_5482828 2815326109929579643934939 := by
  unfold tailWord_5482828
  simp only [CollatzResearch.WordTrace]
  refine ⟨99987582890329011658748569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133316777187105348878331425 99987582890329011658748569)
  ·
    refine ⟨74990687167746758744061427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99987582890329011658748569 74990687167746758744061427)
    ·
      refine ⟨112486030751620138116092141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74990687167746758744061427 112486030751620138116092141)
      ·
        refine ⟨42182261531857551793534553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112486030751620138116092141 42182261531857551793534553)
        ·
          refine ⟨31636696148893163845150915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42182261531857551793534553 31636696148893163845150915)
          ·
            refine ⟨47455044223339745767726373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31636696148893163845150915 47455044223339745767726373)
            ·
              refine ⟨8897820791876202331448695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47455044223339745767726373 8897820791876202331448695)
              ·
                refine ⟨13346731187814303497173043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8897820791876202331448695 13346731187814303497173043)
                ·
                  refine ⟨20020096781721455245759565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13346731187814303497173043 20020096781721455245759565)
                  ·
                    refine ⟨7507536293145545717159837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20020096781721455245759565 7507536293145545717159837)
                    ·
                      refine ⟨2815326109929579643934939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7507536293145545717159837 2815326109929579643934939)
                      ·
                        rfl

theorem cell23_5482828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_5482828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482828 prefixEnd_5482828 := by exact prefixLift 5482828
  have htrace : WordTrace (prefixWord ++ tailWord_5482828) baseStart_5482828 baseEnd_5482828 := by
    simpa [prefixWord, tailWord_5482828, baseEnd_5482828] using wordTrace_append hprefix tailTrace_5482828
  have hstable : (prefixWord ++ tailWord_5482828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482828).length < 2 ^ (prefixWord ++ tailWord_5482828).sum := by decide
  have hdescent : baseEnd_5482828 < baseStart_5482828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482846 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5482846 : Nat := 118140960795 + 5482846 * 2 ^ 59
def prefixEnd_5482846 : Nat := 4983230072969 + 3 ^ 40 * 5482846 * 2
def baseEnd_5482846 : Nat := 2815335352581360573509857

theorem tailTrace_5482846 : CollatzResearch.WordTrace tailWord_5482846 prefixEnd_5482846 2815335352581360573509857 := by
  unfold tailWord_5482846
  simp only [CollatzResearch.WordTrace]
  refine ⟨24996977786824101548956549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133317214863061874927768261 24996977786824101548956549)
  ·
    refine ⟨4686933335029519040429353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24996977786824101548956549 4686933335029519040429353)
    ·
      refine ⟨3515200001272139280322015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4686933335029519040429353 3515200001272139280322015)
      ·
        refine ⟨5272800001908208920483023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515200001272139280322015 5272800001908208920483023)
        ·
          refine ⟨7909200002862313380724535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5272800001908208920483023 7909200002862313380724535)
          ·
            refine ⟨11863800004293470071086803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7909200002862313380724535 11863800004293470071086803)
            ·
              refine ⟨17795700006440205106630205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11863800004293470071086803 17795700006440205106630205)
              ·
                refine ⟨6673387502415076914986327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17795700006440205106630205 6673387502415076914986327)
                ·
                  refine ⟨10010081253622615372479491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6673387502415076914986327 10010081253622615372479491)
                  ·
                    refine ⟨15015121880433923058719237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10010081253622615372479491 15015121880433923058719237)
                    ·
                      refine ⟨2815335352581360573509857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15015121880433923058719237 2815335352581360573509857)
                      ·
                        rfl

theorem cell23_5482846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5482846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482846 prefixEnd_5482846 := by exact prefixLift 5482846
  have htrace : WordTrace (prefixWord ++ tailWord_5482846) baseStart_5482846 baseEnd_5482846 := by
    simpa [prefixWord, tailWord_5482846, baseEnd_5482846] using wordTrace_append hprefix tailTrace_5482846
  have hstable : (prefixWord ++ tailWord_5482846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482846).length < 2 ^ (prefixWord ++ tailWord_5482846).sum := by decide
  have hdescent : baseEnd_5482846 < baseStart_5482846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482861 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_5482861 : Nat := 118140960795 + 5482861 * 2 ^ 59
def prefixEnd_5482861 : Nat := 4983230072969 + 3 ^ 40 * 5482861 * 2
def baseEnd_5482861 : Nat := 938447684930392671607429

theorem tailTrace_5482861 : CollatzResearch.WordTrace tailWord_5482861 prefixEnd_5482861 938447684930392671607429 := by
  unfold tailWord_5482861
  simp only [CollatzResearch.WordTrace]
  refine ⟨199976369389538469953448437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133317579593025646635632291 199976369389538469953448437)
  ·
    refine ⟨18747784630269231558135791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199976369389538469953448437 18747784630269231558135791)
    ·
      refine ⟨28121676945403847337203687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18747784630269231558135791 28121676945403847337203687)
      ·
        refine ⟨42182515418105771005805531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28121676945403847337203687 42182515418105771005805531)
        ·
          refine ⟨63273773127158656508708297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42182515418105771005805531 63273773127158656508708297)
          ·
            refine ⟨47455329845368992381531223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63273773127158656508708297 47455329845368992381531223)
            ·
              refine ⟨71182994768053488572296835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47455329845368992381531223 71182994768053488572296835)
              ·
                refine ⟨106774492152080232858445253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71182994768053488572296835 106774492152080232858445253)
                ·
                  refine ⟨20020217278515043660958485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106774492152080232858445253 20020217278515043660958485)
                  ·
                    refine ⟨938447684930392671607429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20020217278515043660958485 938447684930392671607429)
                    ·
                      rfl

theorem cell23_5482861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_5482861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482861 prefixEnd_5482861 := by exact prefixLift 5482861
  have htrace : WordTrace (prefixWord ++ tailWord_5482861) baseStart_5482861 baseEnd_5482861 := by
    simpa [prefixWord, tailWord_5482861, baseEnd_5482861] using wordTrace_append hprefix tailTrace_5482861
  have hstable : (prefixWord ++ tailWord_5482861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482861).length < 2 ^ (prefixWord ++ tailWord_5482861).sum := by decide
  have hdescent : baseEnd_5482861 < baseStart_5482861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482871 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_5482871 : Nat := 118140960795 + 5482871 * 2 ^ 59
def prefixEnd_5482871 : Nat := 4983230072969 + 3 ^ 40 * 5482871 * 2
def baseEnd_5482871 : Nat := 2815348189597722975697241

theorem tailTrace_5482871 : CollatzResearch.WordTrace tailWord_5482871 prefixEnd_5482871 2815348189597722975697241 := by
  unfold tailWord_5482871
  simp only [CollatzResearch.WordTrace]
  refine ⟨199976734119502241661312467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133317822746334827774208311 199976734119502241661312467)
  ·
    refine ⟨299965101179253362491968701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199976734119502241661312467 299965101179253362491968701)
    ·
      refine ⟨112486912942220010934488263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299965101179253362491968701 112486912942220010934488263)
      ·
        refine ⟨168730369413330016401732395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112486912942220010934488263 168730369413330016401732395)
        ·
          refine ⟨253095554119995024602598593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168730369413330016401732395 253095554119995024602598593)
          ·
            refine ⟨189821665589996268451948945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253095554119995024602598593 189821665589996268451948945)
            ·
              refine ⟨142366249192497201338961709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189821665589996268451948945 142366249192497201338961709)
              ·
                refine ⟨53387343447186450502110641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142366249192497201338961709 53387343447186450502110641)
                ·
                  refine ⟨40040507585389837876582981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53387343447186450502110641 40040507585389837876582981)
                  ·
                    refine ⟨7507595172260594601859309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40040507585389837876582981 7507595172260594601859309)
                    ·
                      refine ⟨2815348189597722975697241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7507595172260594601859309 2815348189597722975697241)
                      ·
                        rfl

theorem cell23_5482871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_5482871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482871 prefixEnd_5482871 := by exact prefixLift 5482871
  have htrace : WordTrace (prefixWord ++ tailWord_5482871) baseStart_5482871 baseEnd_5482871 := by
    simpa [prefixWord, tailWord_5482871, baseEnd_5482871] using wordTrace_append hprefix tailTrace_5482871
  have hstable : (prefixWord ++ tailWord_5482871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482871).length < 2 ^ (prefixWord ++ tailWord_5482871).sum := by decide
  have hdescent : baseEnd_5482871 < baseStart_5482871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5482891 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 7]
def baseStart_5482891 : Nat := 118140960795 + 5482891 * 2 ^ 59
def prefixEnd_5482891 : Nat := 4983230072969 + 3 ^ 40 * 5482891 * 2
def baseEnd_5482891 : Nat := 312817606578979210827461

theorem tailTrace_5482891 : CollatzResearch.WordTrace tailWord_5482891 prefixEnd_5482891 312817606578979210827461 := by
  unfold tailWord_5482891
  simp only [CollatzResearch.WordTrace]
  refine ⟨199977463579429785077040527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133318309052953190051360351 199977463579429785077040527)
  ·
    refine ⟨299966195369144677615560791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199977463579429785077040527 299966195369144677615560791)
    ·
      refine ⟨449949293053717016423341187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299966195369144677615560791 449949293053717016423341187)
      ·
        refine ⟨674923939580575524635011781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449949293053717016423341187 674923939580575524635011781)
        ·
          refine ⟨126548238671357910869064709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 674923939580575524635011781 126548238671357910869064709)
          ·
            refine ⟨23727794750879608287949633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126548238671357910869064709 23727794750879608287949633)
            ·
              refine ⟨17795846063159706215962225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23727794750879608287949633 17795846063159706215962225)
              ·
                refine ⟨13346884547369779661971669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17795846063159706215962225 13346884547369779661971669)
                ·
                  refine ⟨312817606578979210827461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13346884547369779661971669 312817606578979210827461)
                  ·
                    rfl

theorem cell23_5482891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 7].length) (baseStart_5482891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5482891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5482891 prefixEnd_5482891 := by exact prefixLift 5482891
  have htrace : WordTrace (prefixWord ++ tailWord_5482891) baseStart_5482891 baseEnd_5482891 := by
    simpa [prefixWord, tailWord_5482891, baseEnd_5482891] using wordTrace_append hprefix tailTrace_5482891
  have hstable : (prefixWord ++ tailWord_5482891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5482891).length < 2 ^ (prefixWord ++ tailWord_5482891).sum := by decide
  have hdescent : baseEnd_5482891 < baseStart_5482891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5482891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483012 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5483012 : Nat := 118140960795 + 5483012 * 2 ^ 59
def prefixEnd_5483012 : Nat := 4983230072969 + 3 ^ 40 * 5483012 * 2
def baseEnd_5483012 : Nat := 2815420590370006924034093

theorem tailTrace_5483012 : CollatzResearch.WordTrace tailWord_5483012 prefixEnd_5483012 2815420590370006924034093 := by
  unfold tailWord_5483012
  simp only [CollatzResearch.WordTrace]
  refine ⟨99990938405995711371097645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133321251207994281828130193 99990938405995711371097645)
  ·
    refine ⟨37496601902248391764161617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99990938405995711371097645 37496601902248391764161617)
    ·
      refine ⟨28122451426686293823121213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37496601902248391764161617 28122451426686293823121213)
      ·
        refine ⟨10545919285007360183670455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28122451426686293823121213 10545919285007360183670455)
        ·
          refine ⟨15818878927511040275505683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10545919285007360183670455 15818878927511040275505683)
          ·
            refine ⟨23728318391266560413258525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15818878927511040275505683 23728318391266560413258525)
            ·
              refine ⟨8898119396724960154971947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23728318391266560413258525 8898119396724960154971947)
              ·
                refine ⟨13347179095087440232457921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8898119396724960154971947 13347179095087440232457921)
                ·
                  refine ⟨10010384321315580174343441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13347179095087440232457921 10010384321315580174343441)
                  ·
                    refine ⟨7507788240986685130757581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10010384321315580174343441 7507788240986685130757581)
                    ·
                      refine ⟨2815420590370006924034093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7507788240986685130757581 2815420590370006924034093)
                      ·
                        rfl

theorem cell23_5483012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5483012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483012 prefixEnd_5483012 := by exact prefixLift 5483012
  have htrace : WordTrace (prefixWord ++ tailWord_5483012) baseStart_5483012 baseEnd_5483012 := by
    simpa [prefixWord, tailWord_5483012, baseEnd_5483012] using wordTrace_append hprefix tailTrace_5483012
  have hstable : (prefixWord ++ tailWord_5483012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483012).length < 2 ^ (prefixWord ++ tailWord_5483012).sum := by decide
  have hdescent : baseEnd_5483012 < baseStart_5483012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483062 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5483062 : Nat := 118140960795 + 5483062 * 2 ^ 59
def prefixEnd_5483062 : Nat := 4983230072969 + 3 ^ 40 * 5483062 * 2
def baseEnd_5483062 : Nat := 938482088134243909469621

theorem tailTrace_5483062 : CollatzResearch.WordTrace tailWord_5483062 prefixEnd_5483062 938482088134243909469621 := by
  unfold tailWord_5483062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12498981278863142580094715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133322466974540187521010293 12498981278863142580094715)
  ·
    refine ⟨18748471918294713870142073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12498981278863142580094715 18748471918294713870142073)
    ·
      refine ⟨14061353938721035402606555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18748471918294713870142073 14061353938721035402606555)
      ·
        refine ⟨21092030908081553103909833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14061353938721035402606555 21092030908081553103909833)
        ·
          refine ⟨15819023181061164827932375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21092030908081553103909833 15819023181061164827932375)
          ·
            refine ⟨23728534771591747241898563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15819023181061164827932375 23728534771591747241898563)
            ·
              refine ⟨35592802157387620862847845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23728534771591747241898563 35592802157387620862847845)
              ·
                refine ⟨6673650404510178911783971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35592802157387620862847845 6673650404510178911783971)
                ·
                  refine ⟨10010475606765268367675957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6673650404510178911783971 10010475606765268367675957)
                  ·
                    refine ⟨938482088134243909469621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10010475606765268367675957 938482088134243909469621)
                    ·
                      rfl

theorem cell23_5483062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5483062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483062 prefixEnd_5483062 := by exact prefixLift 5483062
  have htrace : WordTrace (prefixWord ++ tailWord_5483062) baseStart_5483062 baseEnd_5483062 := by
    simpa [prefixWord, tailWord_5483062, baseEnd_5483062] using wordTrace_append hprefix tailTrace_5483062
  have hstable : (prefixWord ++ tailWord_5483062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483062).length < 2 ^ (prefixWord ++ tailWord_5483062).sum := by decide
  have hdescent : baseEnd_5483062 < baseStart_5483062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483065 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5483065 : Nat := 118140960795 + 5483065 * 2 ^ 59
def prefixEnd_5483065 : Nat := 4983230072969 + 3 ^ 40 * 5483065 * 2
def baseEnd_5483065 : Nat := 2815447804844695216671349

theorem tailTrace_5483065 : CollatzResearch.WordTrace tailWord_5483065 prefixEnd_5483065 2815447804844695216671349 := by
  unfold tailWord_5483065
  simp only [CollatzResearch.WordTrace]
  refine ⟨199983809880799412793874649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133322539920532941862583099 199983809880799412793874649)
  ·
    refine ⟨149987857410599559595405987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199983809880799412793874649 149987857410599559595405987)
    ·
      refine ⟨224981786115899339393108981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149987857410599559595405987 224981786115899339393108981)
      ·
        refine ⟨21092042448365563068103967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224981786115899339393108981 21092042448365563068103967)
        ·
          refine ⟨31638063672548344602155951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21092042448365563068103967 31638063672548344602155951)
          ·
            refine ⟨47457095508822516903233927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31638063672548344602155951 47457095508822516903233927)
            ·
              refine ⟨71185643263233775354850891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47457095508822516903233927 71185643263233775354850891)
              ·
                refine ⟨106778464894850663032276337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71185643263233775354850891 106778464894850663032276337)
                ·
                  refine ⟨80083848671137997274207253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106778464894850663032276337 80083848671137997274207253)
                  ·
                    refine ⟨3753930406459593622228465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80083848671137997274207253 3753930406459593622228465)
                    ·
                      refine ⟨2815447804844695216671349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3753930406459593622228465 2815447804844695216671349)
                      ·
                        rfl

theorem cell23_5483065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5483065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483065 prefixEnd_5483065 := by exact prefixLift 5483065
  have htrace : WordTrace (prefixWord ++ tailWord_5483065) baseStart_5483065 baseEnd_5483065 := by
    simpa [prefixWord, tailWord_5483065, baseEnd_5483065] using wordTrace_append hprefix tailTrace_5483065
  have hstable : (prefixWord ++ tailWord_5483065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483065).length < 2 ^ (prefixWord ++ tailWord_5483065).sum := by decide
  have hdescent : baseEnd_5483065 < baseStart_5483065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483108 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_5483108 : Nat := 118140960795 + 5483108 * 2 ^ 59
def prefixEnd_5483108 : Nat := 4983230072969 + 3 ^ 40 * 5483108 * 2
def baseEnd_5483108 : Nat := 2815469884512838548433651

theorem tailTrace_5483108 : CollatzResearch.WordTrace tailWord_5483108 prefixEnd_5483108 2815469884512838548433651 := by
  unfold tailWord_5483108
  simp only [CollatzResearch.WordTrace]
  refine ⟨99992689109821815568844989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133323585479762420758459985 99992689109821815568844989)
  ·
    refine ⟨37497258416183180838316871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99992689109821815568844989 37497258416183180838316871)
    ·
      refine ⟨56245887624274771257475307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37497258416183180838316871 56245887624274771257475307)
      ·
        refine ⟨84368831436412156886212961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56245887624274771257475307 84368831436412156886212961)
        ·
          refine ⟨63276623577309117664659721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84368831436412156886212961 63276623577309117664659721)
          ·
            refine ⟨47457467682981838248494791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63276623577309117664659721 47457467682981838248494791)
            ·
              refine ⟨71186201524472757372742187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47457467682981838248494791 71186201524472757372742187)
              ·
                refine ⟨106779302286709136059113281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71186201524472757372742187 106779302286709136059113281)
                ·
                  refine ⟨80084476715031852044334961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106779302286709136059113281 80084476715031852044334961)
                  ·
                    refine ⟨60063357536273889033251221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80084476715031852044334961 60063357536273889033251221)
                    ·
                      refine ⟨2815469884512838548433651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60063357536273889033251221 2815469884512838548433651)
                      ·
                        rfl

theorem cell23_5483108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_5483108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483108 prefixEnd_5483108 := by exact prefixLift 5483108
  have htrace : WordTrace (prefixWord ++ tailWord_5483108) baseStart_5483108 baseEnd_5483108 := by
    simpa [prefixWord, tailWord_5483108, baseEnd_5483108] using wordTrace_append hprefix tailTrace_5483108
  have hstable : (prefixWord ++ tailWord_5483108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483108).length < 2 ^ (prefixWord ++ tailWord_5483108).sum := by decide
  have hdescent : baseEnd_5483108 < baseStart_5483108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483115 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 3]
def baseStart_5483115 : Nat := 118140960795 + 5483115 * 2 ^ 59
def prefixEnd_5483115 : Nat := 4983230072969 + 3 ^ 40 * 5483115 * 2
def baseEnd_5483115 : Nat := 2815473478877420021046119

theorem tailTrace_5483115 : CollatzResearch.WordTrace tailWord_5483115 prefixEnd_5483115 2815473478877420021046119 := by
  unfold tailWord_5483115
  simp only [CollatzResearch.WordTrace]
  refine ⟨199985633530618271333194799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133323755687078847555463199 199985633530618271333194799)
  ·
    refine ⟨299978450295927406999792199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199985633530618271333194799 299978450295927406999792199)
    ·
      refine ⟨449967675443891110499688299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299978450295927406999792199 449967675443891110499688299)
      ·
        refine ⟨674951513165836665749532449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449967675443891110499688299 674951513165836665749532449)
        ·
          refine ⟨506213634874377499312149337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674951513165836665749532449 506213634874377499312149337)
          ·
            refine ⟨379660226155783124484112003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506213634874377499312149337 379660226155783124484112003)
            ·
              refine ⟨569490339233674686726168005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379660226155783124484112003 569490339233674686726168005)
              ·
                refine ⟨106779438606314003761156501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569490339233674686726168005 106779438606314003761156501)
                ·
                  refine ⟨5005286184670968926304211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106779438606314003761156501 5005286184670968926304211)
                  ·
                    refine ⟨7507929277006453389456317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5005286184670968926304211 7507929277006453389456317)
                    ·
                      refine ⟨2815473478877420021046119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7507929277006453389456317 2815473478877420021046119)
                      ·
                        rfl

theorem cell23_5483115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 1, 3].length) (baseStart_5483115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483115 prefixEnd_5483115 := by exact prefixLift 5483115
  have htrace : WordTrace (prefixWord ++ tailWord_5483115) baseStart_5483115 baseEnd_5483115 := by
    simpa [prefixWord, tailWord_5483115, baseEnd_5483115] using wordTrace_append hprefix tailTrace_5483115
  have hstable : (prefixWord ++ tailWord_5483115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483115).length < 2 ^ (prefixWord ++ tailWord_5483115).sum := by decide
  have hdescent : baseEnd_5483115 < baseStart_5483115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483189 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_5483189 : Nat := 118140960795 + 5483189 * 2 ^ 59
def prefixEnd_5483189 : Nat := 4983230072969 + 3 ^ 40 * 5483189 * 2
def baseEnd_5483189 : Nat := 2815511476445852731520779

theorem tailTrace_5483189 : CollatzResearch.WordTrace tailWord_5483189 prefixEnd_5483189 2815511476445852731520779 := by
  unfold tailWord_5483189
  simp only [CollatzResearch.WordTrace]
  refine ⟨199988332532350181971388621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133325555021566787980925747 199988332532350181971388621)
  ·
    refine ⟨74995624699631318239270733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199988332532350181971388621 74995624699631318239270733)
    ·
      refine ⟨28123359262361744339726525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74995624699631318239270733 28123359262361744339726525)
      ·
        refine ⟨10546259723385654127397447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28123359262361744339726525 10546259723385654127397447)
        ·
          refine ⟨15819389585078481191096171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546259723385654127397447 15819389585078481191096171)
          ·
            refine ⟨23729084377617721786644257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15819389585078481191096171 23729084377617721786644257)
            ·
              refine ⟨17796813283213291339983193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23729084377617721786644257 17796813283213291339983193)
              ·
                refine ⟨13347609962409968504987395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17796813283213291339983193 13347609962409968504987395)
                ·
                  refine ⟨20021414943614952757481093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13347609962409968504987395 20021414943614952757481093)
                  ·
                    refine ⟨3754015301927803642027705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20021414943614952757481093 3754015301927803642027705)
                    ·
                      refine ⟨2815511476445852731520779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754015301927803642027705 2815511476445852731520779)
                      ·
                        rfl

theorem cell23_5483189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_5483189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483189 prefixEnd_5483189 := by exact prefixLift 5483189
  have htrace : WordTrace (prefixWord ++ tailWord_5483189) baseStart_5483189 baseEnd_5483189 := by
    simpa [prefixWord, tailWord_5483189, baseEnd_5483189] using wordTrace_append hprefix tailTrace_5483189
  have hstable : (prefixWord ++ tailWord_5483189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483189).length < 2 ^ (prefixWord ++ tailWord_5483189).sum := by decide
  have hdescent : baseEnd_5483189 < baseStart_5483189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483212 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 7]
def baseStart_5483212 : Nat := 118140960795 + 5483212 * 2 ^ 59
def prefixEnd_5483212 : Nat := 4983230072969 + 3 ^ 40 * 5483212 * 2
def baseEnd_5483212 : Nat := 312835920722322904614797

theorem tailTrace_5483212 : CollatzResearch.WordTrace tailWord_5483212 prefixEnd_5483212 312835920722322904614797 := by
  unfold tailWord_5483212
  simp only [CollatzResearch.WordTrace]
  refine ⟨99994585705633428449737945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133326114274177904599650593 99994585705633428449737945)
  ·
    refine ⟨74995939279225071337303459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99994585705633428449737945 74995939279225071337303459)
    ·
      refine ⟨112493908918837607005955189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74995939279225071337303459 112493908918837607005955189)
      ·
        refine ⟨10546303961141025656808299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112493908918837607005955189 10546303961141025656808299)
        ·
          refine ⟨15819455941711538485212449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546303961141025656808299 15819455941711538485212449)
          ·
            refine ⟨11864591956283653863909337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15819455941711538485212449 11864591956283653863909337)
            ·
              refine ⟨8898443967212740397932003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11864591956283653863909337 8898443967212740397932003)
              ·
                refine ⟨13347665950819110596898005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8898443967212740397932003 13347665950819110596898005)
                ·
                  refine ⟨312835920722322904614797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13347665950819110596898005 312835920722322904614797)
                  ·
                    rfl

theorem cell23_5483212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_5483212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483212 prefixEnd_5483212 := by exact prefixLift 5483212
  have htrace : WordTrace (prefixWord ++ tailWord_5483212) baseStart_5483212 baseEnd_5483212 := by
    simpa [prefixWord, tailWord_5483212, baseEnd_5483212] using wordTrace_append hprefix tailTrace_5483212
  have hstable : (prefixWord ++ tailWord_5483212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483212).length < 2 ^ (prefixWord ++ tailWord_5483212).sum := by decide
  have hdescent : baseEnd_5483212 < baseStart_5483212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483356 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5483356 : Nat := 118140960795 + 5483356 * 2 ^ 59
def prefixEnd_5483356 : Nat := 4983230072969 + 3 ^ 40 * 5483356 * 2
def baseEnd_5483356 : Nat := 2815597227715153578132511

theorem tailTrace_5483356 : CollatzResearch.WordTrace tailWord_5483356 prefixEnd_5483356 2815597227715153578132511 := by
  unfold tailWord_5483356
  simp only [CollatzResearch.WordTrace]
  refine ⟨99997211761372584746358961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133329615681830112995145281 99997211761372584746358961)
  ·
    refine ⟨74997908821029438559769221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99997211761372584746358961 74997908821029438559769221)
    ·
      refine ⟨14062107903943019729956729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74997908821029438559769221 14062107903943019729956729)
      ·
        refine ⟨10546580927957264797467547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14062107903943019729956729 10546580927957264797467547)
        ·
          refine ⟨15819871391935897196201321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546580927957264797467547 15819871391935897196201321)
          ·
            refine ⟨11864903543951922897150991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15819871391935897196201321 11864903543951922897150991)
            ·
              refine ⟨17797355315927884345726487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11864903543951922897150991 17797355315927884345726487)
              ·
                refine ⟨26696032973891826518589731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17797355315927884345726487 26696032973891826518589731)
                ·
                  refine ⟨40044049460837739777884597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26696032973891826518589731 40044049460837739777884597)
                  ·
                    refine ⟨3754129636953538104176681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40044049460837739777884597 3754129636953538104176681)
                    ·
                      refine ⟨2815597227715153578132511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754129636953538104176681 2815597227715153578132511)
                      ·
                        rfl

theorem cell23_5483356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5483356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483356 prefixEnd_5483356 := by exact prefixLift 5483356
  have htrace : WordTrace (prefixWord ++ tailWord_5483356) baseStart_5483356 baseEnd_5483356 := by
    simpa [prefixWord, tailWord_5483356, baseEnd_5483356] using wordTrace_append hprefix tailTrace_5483356
  have hstable : (prefixWord ++ tailWord_5483356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483356).length < 2 ^ (prefixWord ++ tailWord_5483356).sum := by decide
  have hdescent : baseEnd_5483356 < baseStart_5483356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483363 : List Nat := [1, 1, 1, 5, 3, 2, 2, 3, 1, 1, 3]
def baseStart_5483363 : Nat := 118140960795 + 5483363 * 2 ^ 59
def prefixEnd_5483363 : Nat := 4983230072969 + 3 ^ 40 * 5483363 * 2
def baseEnd_5483363 : Nat := 2815600822079735050744979

theorem tailTrace_5483363 : CollatzResearch.WordTrace tailWord_5483363 prefixEnd_5483363 2815600822079735050744979 := by
  unfold tailWord_5483363
  simp only [CollatzResearch.WordTrace]
  refine ⟨199994678833719809688222743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133329785889146539792148495 199994678833719809688222743)
  ·
    refine ⟨299992018250579714532334115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199994678833719809688222743 299992018250579714532334115)
    ·
      refine ⟨449988027375869571798501173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299992018250579714532334115 449988027375869571798501173)
      ·
        refine ⟨42186377566487772356109485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 449988027375869571798501173 42186377566487772356109485)
        ·
          refine ⟨15819891587432914633541057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42186377566487772356109485 15819891587432914633541057)
          ·
            refine ⟨11864918690574685975155793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15819891587432914633541057 11864918690574685975155793)
            ·
              refine ⟨8898689017931014481366845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11864918690574685975155793 8898689017931014481366845)
              ·
                refine ⟨3337008381724130430512567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8898689017931014481366845 3337008381724130430512567)
                ·
                  refine ⟨5005512572586195645768851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337008381724130430512567 5005512572586195645768851)
                  ·
                    refine ⟨7508268858879293468653277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5005512572586195645768851 7508268858879293468653277)
                    ·
                      refine ⟨2815600822079735050744979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7508268858879293468653277 2815600822079735050744979)
                      ·
                        rfl

theorem cell23_5483363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_5483363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483363 prefixEnd_5483363 := by exact prefixLift 5483363
  have htrace : WordTrace (prefixWord ++ tailWord_5483363) baseStart_5483363 baseEnd_5483363 := by
    simpa [prefixWord, tailWord_5483363, baseEnd_5483363] using wordTrace_append hprefix tailTrace_5483363
  have hstable : (prefixWord ++ tailWord_5483363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483363).length < 2 ^ (prefixWord ++ tailWord_5483363).sum := by decide
  have hdescent : baseEnd_5483363 < baseStart_5483363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483372 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_5483372 : Nat := 118140960795 + 5483372 * 2 ^ 59
def prefixEnd_5483372 : Nat := 4983230072969 + 3 ^ 40 * 5483372 * 2
def baseEnd_5483372 : Nat := 2815605443405625515532437

theorem tailTrace_5483372 : CollatzResearch.WordTrace tailWord_5483372 prefixEnd_5483372 2815605443405625515532437 := by
  unfold tailWord_5483372
  simp only [CollatzResearch.WordTrace]
  refine ⟨99997503545343602112650185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133330004727124802816866913 99997503545343602112650185)
  ·
    refine ⟨74998127659007701584487639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99997503545343602112650185 74998127659007701584487639)
    ·
      refine ⟨112497191488511552376731459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74998127659007701584487639 112497191488511552376731459)
      ·
        refine ⟨168745787232767328565097189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112497191488511552376731459 168745787232767328565097189)
        ·
          refine ⟨31639835106143874105955723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168745787232767328565097189 31639835106143874105955723)
          ·
            refine ⟨47459752659215811158933585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31639835106143874105955723 47459752659215811158933585)
            ·
              refine ⟨35594814494411858369200189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47459752659215811158933585 35594814494411858369200189)
              ·
                refine ⟨13348055435404446888450071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35594814494411858369200189 13348055435404446888450071)
                ·
                  refine ⟨20022083153106670332675107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13348055435404446888450071 20022083153106670332675107)
                  ·
                    refine ⟨30033124729660005499012661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20022083153106670332675107 30033124729660005499012661)
                    ·
                      refine ⟨2815605443405625515532437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30033124729660005499012661 2815605443405625515532437)
                      ·
                        rfl

theorem cell23_5483372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_5483372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483372 prefixEnd_5483372 := by exact prefixLift 5483372
  have htrace : WordTrace (prefixWord ++ tailWord_5483372) baseStart_5483372 baseEnd_5483372 := by
    simpa [prefixWord, tailWord_5483372, baseEnd_5483372] using wordTrace_append hprefix tailTrace_5483372
  have hstable : (prefixWord ++ tailWord_5483372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483372).length < 2 ^ (prefixWord ++ tailWord_5483372).sum := by decide
  have hdescent : baseEnd_5483372 < baseStart_5483372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483379 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 2, 4]
def baseStart_5483379 : Nat := 118140960795 + 5483379 * 2 ^ 59
def prefixEnd_5483379 : Nat := 4983230072969 + 3 ^ 40 * 5483379 * 2
def baseEnd_5483379 : Nat := 938536345923402329381635

theorem tailTrace_5483379 : CollatzResearch.WordTrace tailWord_5483379 prefixEnd_5483379 938536345923402329381635 := by
  unfold tailWord_5483379
  simp only [CollatzResearch.WordTrace]
  refine ⟨199995262401661844420805191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133330174934441229613870127 199995262401661844420805191)
  ·
    refine ⟨299992893602492766631207787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199995262401661844420805191 299992893602492766631207787)
    ·
      refine ⟨449989340403739149946811681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299992893602492766631207787 449989340403739149946811681)
      ·
        refine ⟨337492005302804362460108761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449989340403739149946811681 337492005302804362460108761)
        ·
          refine ⟨253119003977103271845081571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337492005302804362460108761 253119003977103271845081571)
          ·
            refine ⟨379678505965654907767622357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253119003977103271845081571 379678505965654907767622357)
            ·
              refine ⟨8898714983570036900803649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 379678505965654907767622357 8898714983570036900803649)
              ·
                refine ⟨6674036237677527675602737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8898714983570036900803649 6674036237677527675602737)
                ·
                  refine ⟨5005527178258145756702053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674036237677527675602737 5005527178258145756702053)
                  ·
                    refine ⟨938536345923402329381635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005527178258145756702053 938536345923402329381635)
                    ·
                      rfl

theorem cell23_5483379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 4].length) (baseStart_5483379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483379 prefixEnd_5483379 := by exact prefixLift 5483379
  have htrace : WordTrace (prefixWord ++ tailWord_5483379) baseStart_5483379 baseEnd_5483379 := by
    simpa [prefixWord, tailWord_5483379, baseEnd_5483379] using wordTrace_append hprefix tailTrace_5483379
  have hstable : (prefixWord ++ tailWord_5483379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483379).length < 2 ^ (prefixWord ++ tailWord_5483379).sum := by decide
  have hdescent : baseEnd_5483379 < baseStart_5483379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483399 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_5483399 : Nat := 118140960795 + 5483399 * 2 ^ 59
def prefixEnd_5483399 : Nat := 4983230072969 + 3 ^ 40 * 5483399 * 2
def baseEnd_5483399 : Nat := 2815619307383296909894813

theorem tailTrace_5483399 : CollatzResearch.WordTrace tailWord_5483399 prefixEnd_5483399 2815619307383296909894813 := by
  unfold tailWord_5483399
  simp only [CollatzResearch.WordTrace]
  refine ⟨199995991861589387836533251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133330661241059591891022167 199995991861589387836533251)
  ·
    refine ⟨299993987792384081754799877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199995991861589387836533251 299993987792384081754799877)
    ·
      refine ⟨56248872711072015329024977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299993987792384081754799877 56248872711072015329024977)
      ·
        refine ⟨42186654533304011496768733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56248872711072015329024977 42186654533304011496768733)
        ·
          refine ⟨15819995449989004311288275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42186654533304011496768733 15819995449989004311288275)
          ·
            refine ⟨23729993174983506466932413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15819995449989004311288275 23729993174983506466932413)
            ·
              refine ⟨8898747440618814925099655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23729993174983506466932413 8898747440618814925099655)
              ·
                refine ⟨13348121160928222387649483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8898747440618814925099655 13348121160928222387649483)
                ·
                  refine ⟨20022181741392333581474225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13348121160928222387649483 20022181741392333581474225)
                  ·
                    refine ⟨15016636306044250186105669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20022181741392333581474225 15016636306044250186105669)
                    ·
                      refine ⟨2815619307383296909894813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15016636306044250186105669 2815619307383296909894813)
                      ·
                        rfl

theorem cell23_5483399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_5483399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483399 prefixEnd_5483399 := by exact prefixLift 5483399
  have htrace : WordTrace (prefixWord ++ tailWord_5483399) baseStart_5483399 baseEnd_5483399 := by
    simpa [prefixWord, tailWord_5483399, baseEnd_5483399] using wordTrace_append hprefix tailTrace_5483399
  have hstable : (prefixWord ++ tailWord_5483399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483399).length < 2 ^ (prefixWord ++ tailWord_5483399).sum := by decide
  have hdescent : baseEnd_5483399 < baseStart_5483399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483414 : List Nat := [5, 3, 1, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5483414 : Nat := 118140960795 + 5483414 * 2 ^ 59
def prefixEnd_5483414 : Nat := 4983230072969 + 3 ^ 40 * 5483414 * 2
def baseEnd_5483414 : Nat := 2815627009593114351207245

theorem tailTrace_5483414 : CollatzResearch.WordTrace tailWord_5483414 prefixEnd_5483414 2815627009593114351207245 := by
  unfold tailWord_5483414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499783684783440337395581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133331025971023363598886197 12499783684783440337395581)
  ·
    refine ⟨4687418881793790126523343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12499783684783440337395581 4687418881793790126523343)
    ·
      refine ⟨7031128322690685189785015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687418881793790126523343 7031128322690685189785015)
      ·
        refine ⟨10546692484036027784677523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7031128322690685189785015 10546692484036027784677523)
        ·
          refine ⟨15820038726054041677016285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546692484036027784677523 15820038726054041677016285)
          ·
            refine ⟨5932514522270265628881107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15820038726054041677016285 5932514522270265628881107)
            ·
              refine ⟨8898771783405398443321661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932514522270265628881107 8898771783405398443321661)
              ·
                refine ⟨3337039418777024416245623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8898771783405398443321661 3337039418777024416245623)
                ·
                  refine ⟨5005559128165536624368435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337039418777024416245623 5005559128165536624368435)
                  ·
                    refine ⟨7508338692248304936552653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5005559128165536624368435 7508338692248304936552653)
                    ·
                      refine ⟨2815627009593114351207245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7508338692248304936552653 2815627009593114351207245)
                      ·
                        rfl

theorem cell23_5483414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5483414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483414 prefixEnd_5483414 := by exact prefixLift 5483414
  have htrace : WordTrace (prefixWord ++ tailWord_5483414) baseStart_5483414 baseEnd_5483414 := by
    simpa [prefixWord, tailWord_5483414, baseEnd_5483414] using wordTrace_append hprefix tailTrace_5483414
  have hstable : (prefixWord ++ tailWord_5483414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483414).length < 2 ^ (prefixWord ++ tailWord_5483414).sum := by decide
  have hdescent : baseEnd_5483414 < baseStart_5483414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483429 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 7, 3, 2]
def baseStart_5483429 : Nat := 118140960795 + 5483429 * 2 ^ 59
def prefixEnd_5483429 : Nat := 4983230072969 + 3 ^ 40 * 5483429 * 2
def baseEnd_5483429 : Nat := 2815634711802931792519675

theorem tailTrace_5483429 : CollatzResearch.WordTrace tailWord_5483429 prefixEnd_5483429 2815634711802931792519675 := by
  unfold tailWord_5483429
  simp only [CollatzResearch.WordTrace]
  refine ⟨199997086051480702960125341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133331390700987135306750227 199997086051480702960125341)
  ·
    refine ⟨74998907269305263610047003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199997086051480702960125341 74998907269305263610047003)
    ·
      refine ⟨112498360903957895415070505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74998907269305263610047003 112498360903957895415070505)
      ·
        refine ⟨84373770677968421561302879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112498360903957895415070505 84373770677968421561302879)
        ·
          refine ⟨126560656016952632341954319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84373770677968421561302879 126560656016952632341954319)
          ·
            refine ⟨189840984025428948512931479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126560656016952632341954319 189840984025428948512931479)
            ·
              refine ⟨284761476038143422769397219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189840984025428948512931479 284761476038143422769397219)
              ·
                refine ⟨427142214057215134154095829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284761476038143422769397219 427142214057215134154095829)
                ·
                  refine ⟨10011145641965979706736621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 427142214057215134154095829 10011145641965979706736621)
                  ·
                    refine ⟨3754179615737242390026233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10011145641965979706736621 3754179615737242390026233)
                    ·
                      refine ⟨2815634711802931792519675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754179615737242390026233 2815634711802931792519675)
                      ·
                        rfl

theorem cell23_5483429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_5483429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483429 prefixEnd_5483429 := by exact prefixLift 5483429
  have htrace : WordTrace (prefixWord ++ tailWord_5483429) baseStart_5483429 baseEnd_5483429 := by
    simpa [prefixWord, tailWord_5483429, baseEnd_5483429] using wordTrace_append hprefix tailTrace_5483429
  have hstable : (prefixWord ++ tailWord_5483429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483429).length < 2 ^ (prefixWord ++ tailWord_5483429).sum := by decide
  have hdescent : baseEnd_5483429 < baseStart_5483429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483437 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5483437 : Nat := 118140960795 + 5483437 * 2 ^ 59
def prefixEnd_5483437 : Nat := 4983230072969 + 3 ^ 40 * 5483437 * 2
def baseEnd_5483437 : Nat := 2815638819648167761219639

theorem tailTrace_5483437 : CollatzResearch.WordTrace tailWord_5483437 prefixEnd_5483437 2815638819648167761219639 := by
  unfold tailWord_5483437
  simp only [CollatzResearch.WordTrace]
  refine ⟨199997377835451720326416565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133331585223634480217611043 199997377835451720326416565)
  ·
    refine ⟨18749754172073598780601553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199997377835451720326416565 18749754172073598780601553)
    ·
      refine ⟨14062315629055199085451165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18749754172073598780601553 14062315629055199085451165)
      ·
        refine ⟨5273368360895699657044187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14062315629055199085451165 5273368360895699657044187)
        ·
          refine ⟨7910052541343549485566281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273368360895699657044187 7910052541343549485566281)
          ·
            refine ⟨5932539406007662114174711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7910052541343549485566281 5932539406007662114174711)
            ·
              refine ⟨8898809109011493171262067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932539406007662114174711 8898809109011493171262067)
              ·
                refine ⟨13348213663517239756893101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8898809109011493171262067 13348213663517239756893101)
                ·
                  refine ⟨5005580123818964908834913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13348213663517239756893101 5005580123818964908834913)
                  ·
                    refine ⟨3754185092864223681626185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5005580123818964908834913 3754185092864223681626185)
                    ·
                      refine ⟨2815638819648167761219639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754185092864223681626185 2815638819648167761219639)
                      ·
                        rfl

theorem cell23_5483437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5483437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483437 prefixEnd_5483437 := by exact prefixLift 5483437
  have htrace : WordTrace (prefixWord ++ tailWord_5483437) baseStart_5483437 baseEnd_5483437 := by
    simpa [prefixWord, tailWord_5483437, baseEnd_5483437] using wordTrace_append hprefix tailTrace_5483437
  have hstable : (prefixWord ++ tailWord_5483437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483437).length < 2 ^ (prefixWord ++ tailWord_5483437).sum := by decide
  have hdescent : baseEnd_5483437 < baseStart_5483437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483453 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_5483453 : Nat := 118140960795 + 5483453 * 2 ^ 59
def prefixEnd_5483453 : Nat := 4983230072969 + 3 ^ 40 * 5483453 * 2
def baseEnd_5483453 : Nat := 2815647035338639698619565

theorem tailTrace_5483453 : CollatzResearch.WordTrace tailWord_5483453 prefixEnd_5483453 2815647035338639698619565 := by
  unfold tailWord_5483453
  simp only [CollatzResearch.WordTrace]
  refine ⟨199997961403393755058999013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133331974268929170039332675 199997961403393755058999013)
  ·
    refine ⟨37499617763136329073562315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199997961403393755058999013 37499617763136329073562315)
    ·
      refine ⟨56249426644704493610343473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37499617763136329073562315 56249426644704493610343473)
      ·
        refine ⟨42187069983528370207757605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56249426644704493610343473 42187069983528370207757605)
        ·
          refine ⟨7910075621911569413954551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42187069983528370207757605 7910075621911569413954551)
          ·
            refine ⟨11865113432867354120931827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910075621911569413954551 11865113432867354120931827)
            ·
              refine ⟨17797670149301031181397741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865113432867354120931827 17797670149301031181397741)
              ·
                refine ⟨6674126305987886693024153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17797670149301031181397741 6674126305987886693024153)
                ·
                  refine ⟨5005594729490915019768115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674126305987886693024153 5005594729490915019768115)
                  ·
                    refine ⟨7508392094236372529652173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5005594729490915019768115 7508392094236372529652173)
                    ·
                      refine ⟨2815647035338639698619565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7508392094236372529652173 2815647035338639698619565)
                      ·
                        rfl

theorem cell23_5483453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_5483453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483453 prefixEnd_5483453 := by exact prefixLift 5483453
  have htrace : WordTrace (prefixWord ++ tailWord_5483453) baseStart_5483453 baseEnd_5483453 := by
    simpa [prefixWord, tailWord_5483453, baseEnd_5483453] using wordTrace_append hprefix tailTrace_5483453
  have hstable : (prefixWord ++ tailWord_5483453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483453).length < 2 ^ (prefixWord ++ tailWord_5483453).sum := by decide
  have hdescent : baseEnd_5483453 < baseStart_5483453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483472 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_5483472 : Nat := 118140960795 + 5483472 * 2 ^ 59
def prefixEnd_5483472 : Nat := 4983230072969 + 3 ^ 40 * 5483472 * 2
def baseEnd_5483472 : Nat := 2815656791471075124281977

theorem tailTrace_5483472 : CollatzResearch.WordTrace tailWord_5483472 prefixEnd_5483472 2815656791471075124281977 := by
  unfold tailWord_5483472
  simp only [CollatzResearch.WordTrace]
  refine ⟨99999327195162460651970335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133332436260216614202627113 99999327195162460651970335)
  ·
    refine ⟨149998990792743690977955503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99999327195162460651970335 149998990792743690977955503)
    ·
      refine ⟨224998486189115536466933255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149998990792743690977955503 224998486189115536466933255)
      ·
        refine ⟨337497729283673304700399883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224998486189115536466933255 337497729283673304700399883)
        ·
          refine ⟨506246593925509957050599825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337497729283673304700399883 506246593925509957050599825)
          ·
            refine ⟨379684945444132467787949869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506246593925509957050599825 379684945444132467787949869)
            ·
              refine ⟨142381854541549675420481201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379684945444132467787949869 142381854541549675420481201)
              ·
                refine ⟨106786390906162256565360901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142381854541549675420481201 106786390906162256565360901)
                ·
                  refine ⟨20022448294905423106005169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106786390906162256565360901 20022448294905423106005169)
                  ·
                    refine ⟨15016836221179067329503877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20022448294905423106005169 15016836221179067329503877)
                    ·
                      refine ⟨2815656791471075124281977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15016836221179067329503877 2815656791471075124281977)
                      ·
                        rfl

theorem cell23_5483472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_5483472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483472 prefixEnd_5483472 := by exact prefixLift 5483472
  have htrace : WordTrace (prefixWord ++ tailWord_5483472) baseStart_5483472 baseEnd_5483472 := by
    simpa [prefixWord, tailWord_5483472, baseEnd_5483472] using wordTrace_append hprefix tailTrace_5483472
  have hstable : (prefixWord ++ tailWord_5483472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483472).length < 2 ^ (prefixWord ++ tailWord_5483472).sum := by decide
  have hdescent : baseEnd_5483472 < baseStart_5483472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483476 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_5483476 : Nat := 118140960795 + 5483476 * 2 ^ 59
def prefixEnd_5483476 : Nat := 4983230072969 + 3 ^ 40 * 5483476 * 2
def baseEnd_5483476 : Nat := 2815658845393693108631959

theorem tailTrace_5483476 : CollatzResearch.WordTrace tailWord_5483476 prefixEnd_5483476 2815658845393693108631959 := by
  unfold tailWord_5483476
  simp only [CollatzResearch.WordTrace]
  refine ⟨99999400141155214993543141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133332533521540286658057521 99999400141155214993543141)
  ·
    refine ⟨18749887526466602811289339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99999400141155214993543141 18749887526466602811289339)
    ·
      refine ⟨28124831289699904216934009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18749887526466602811289339 28124831289699904216934009)
      ·
        refine ⟨21093623467274928162700507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28124831289699904216934009 21093623467274928162700507)
        ·
          refine ⟨31640435200912392244050761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21093623467274928162700507 31640435200912392244050761)
          ·
            refine ⟨23730326400684294183038071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31640435200912392244050761 23730326400684294183038071)
            ·
              refine ⟨35595489601026441274557107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23730326400684294183038071 35595489601026441274557107)
              ·
                refine ⟨53393234401539661911835661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35595489601026441274557107 53393234401539661911835661)
                ·
                  refine ⟨20022462900577373216938373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53393234401539661911835661 20022462900577373216938373)
                  ·
                    refine ⟨3754211793858257478175945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20022462900577373216938373 3754211793858257478175945)
                    ·
                      refine ⟨2815658845393693108631959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754211793858257478175945 2815658845393693108631959)
                      ·
                        rfl

theorem cell23_5483476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_5483476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483476 prefixEnd_5483476 := by exact prefixLift 5483476
  have htrace : WordTrace (prefixWord ++ tailWord_5483476) baseStart_5483476 baseEnd_5483476 := by
    simpa [prefixWord, tailWord_5483476, baseEnd_5483476] using wordTrace_append hprefix tailTrace_5483476
  have hstable : (prefixWord ++ tailWord_5483476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483476).length < 2 ^ (prefixWord ++ tailWord_5483476).sum := by decide
  have hdescent : baseEnd_5483476 < baseStart_5483476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483510 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_5483510 : Nat := 118140960795 + 5483510 * 2 ^ 59
def prefixEnd_5483510 : Nat := 4983230072969 + 3 ^ 40 * 5483510 * 2
def baseEnd_5483510 : Nat := 2815676303735945975606803

theorem tailTrace_5483510 : CollatzResearch.WordTrace tailWord_5483510 prefixEnd_5483510 2815676303735945975606803 := by
  unfold tailWord_5483510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12500002522761703362113999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133333360242791502529215989 12500002522761703362113999)
  ·
    refine ⟨18750003784142555043170999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12500002522761703362113999 18750003784142555043170999)
    ·
      refine ⟨28125005676213832564756499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18750003784142555043170999 28125005676213832564756499)
      ·
        refine ⟨42187508514320748847134749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28125005676213832564756499 42187508514320748847134749)
        ·
          refine ⟨15820315692870280817675531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42187508514320748847134749 15820315692870280817675531)
          ·
            refine ⟨23730473539305421226513297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15820315692870280817675531 23730473539305421226513297)
            ·
              refine ⟨17797855154479065919884973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23730473539305421226513297 17797855154479065919884973)
              ·
                refine ⟨6674195682929649719956865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17797855154479065919884973 6674195682929649719956865)
                ·
                  refine ⟨5005646762197237289967649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674195682929649719956865 5005646762197237289967649)
                  ·
                    refine ⟨3754235071647927967475737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5005646762197237289967649 3754235071647927967475737)
                    ·
                      refine ⟨2815676303735945975606803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754235071647927967475737 2815676303735945975606803)
                      ·
                        rfl

theorem cell23_5483510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_5483510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483510 prefixEnd_5483510 := by exact prefixLift 5483510
  have htrace : WordTrace (prefixWord ++ tailWord_5483510) baseStart_5483510 baseEnd_5483510 := by
    simpa [prefixWord, tailWord_5483510, baseEnd_5483510] using wordTrace_append hprefix tailTrace_5483510
  have hstable : (prefixWord ++ tailWord_5483510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483510).length < 2 ^ (prefixWord ++ tailWord_5483510).sum := by decide
  have hdescent : baseEnd_5483510 < baseStart_5483510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483512 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 1, 7]
def baseStart_5483512 : Nat := 118140960795 + 5483512 * 2 ^ 59
def prefixEnd_5483512 : Nat := 4983230072969 + 3 ^ 40 * 5483512 * 2
def baseEnd_5483512 : Nat := 938559110232418322593931

theorem tailTrace_5483512 : CollatzResearch.WordTrace tailWord_5483512 prefixEnd_5483512 938559110232418322593931 := by
  unfold tailWord_5483512
  simp only [CollatzResearch.WordTrace]
  refine ⟨100000056655090004067698395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133333408873453338756931193 100000056655090004067698395)
  ·
    refine ⟨150000084982635006101547593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100000056655090004067698395 150000084982635006101547593)
    ·
      refine ⟨112500063736976254576160695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150000084982635006101547593 112500063736976254576160695)
      ·
        refine ⟨168750095605464381864241043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112500063736976254576160695 168750095605464381864241043)
        ·
          refine ⟨253125143408196572796361565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168750095605464381864241043 253125143408196572796361565)
          ·
            refine ⟨94921928778073714798635587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253125143408196572796361565 94921928778073714798635587)
            ·
              refine ⟨142382893167110572197953381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94921928778073714798635587 142382893167110572197953381)
              ·
                refine ⟨26696792468833232287116259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142382893167110572197953381 26696792468833232287116259)
                ·
                  refine ⟨40045188703249848430674389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26696792468833232287116259 40045188703249848430674389)
                  ·
                    refine ⟨938559110232418322593931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40045188703249848430674389 938559110232418322593931)
                    ·
                      rfl

theorem cell23_5483512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_5483512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483512 prefixEnd_5483512 := by exact prefixLift 5483512
  have htrace : WordTrace (prefixWord ++ tailWord_5483512) baseStart_5483512 baseEnd_5483512 := by
    simpa [prefixWord, tailWord_5483512, baseEnd_5483512] using wordTrace_append hprefix tailTrace_5483512
  have hstable : (prefixWord ++ tailWord_5483512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483512).length < 2 ^ (prefixWord ++ tailWord_5483512).sum := by decide
  have hdescent : baseEnd_5483512 < baseStart_5483512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483569 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_5483569 : Nat := 118140960795 + 5483569 * 2 ^ 59
def prefixEnd_5483569 : Nat := 4983230072969 + 3 ^ 40 * 5483569 * 2
def baseEnd_5483569 : Nat := 2815706599094561244769031

theorem tailTrace_5483569 : CollatzResearch.WordTrace tailWord_5483569 prefixEnd_5483569 2815706599094561244769031 := by
  unfold tailWord_5483569
  simp only [CollatzResearch.WordTrace]
  refine ⟨200002192270973506870221761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133334794847315671246814507 200002192270973506870221761)
  ·
    refine ⟨150001644203230130152666321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200002192270973506870221761 150001644203230130152666321)
    ·
      refine ⟨112501233152422597614499741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150001644203230130152666321 112501233152422597614499741)
      ·
        refine ⟨42187962432158474105437403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112501233152422597614499741 42187962432158474105437403)
        ·
          refine ⟨63281943648237711158156105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42187962432158474105437403 63281943648237711158156105)
          ·
            refine ⟨47461457736178283368617079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63281943648237711158156105 47461457736178283368617079)
            ·
              refine ⟨71192186604267425052925619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47461457736178283368617079 71192186604267425052925619)
              ·
                refine ⟨106788279906401137579388429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71192186604267425052925619 106788279906401137579388429)
                ·
                  refine ⟨40045604964900426592270661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106788279906401137579388429 40045604964900426592270661)
                  ·
                    refine ⟨7508550930918829986050749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40045604964900426592270661 7508550930918829986050749)
                    ·
                      refine ⟨2815706599094561244769031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7508550930918829986050749 2815706599094561244769031)
                      ·
                        rfl

theorem cell23_5483569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_5483569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483569 prefixEnd_5483569 := by exact prefixLift 5483569
  have htrace : WordTrace (prefixWord ++ tailWord_5483569) baseStart_5483569 baseEnd_5483569 := by
    simpa [prefixWord, tailWord_5483569, baseEnd_5483569] using wordTrace_append hprefix tailTrace_5483569
  have hstable : (prefixWord ++ tailWord_5483569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483569).length < 2 ^ (prefixWord ++ tailWord_5483569).sum := by decide
  have hdescent : baseEnd_5483569 < baseStart_5483569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483576 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 3, 4]
def baseStart_5483576 : Nat := 118140960795 + 5483576 * 2 ^ 59
def prefixEnd_5483576 : Nat := 4983230072969 + 3 ^ 40 * 5483576 * 2
def baseEnd_5483576 : Nat := 938570064486380905793833

theorem tailTrace_5483576 : CollatzResearch.WordTrace tailWord_5483576 prefixEnd_5483576 938570064486380905793833 := by
  unfold tailWord_5483576
  simp only [CollatzResearch.WordTrace]
  refine ⟨100001223790974073532863291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133334965054632098043817721 100001223790974073532863291)
  ·
    refine ⟨150001835686461110299294937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100001223790974073532863291 150001835686461110299294937)
    ·
      refine ⟨112501376764845832724471203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150001835686461110299294937 112501376764845832724471203)
      ·
        refine ⟨168752065147268749086706805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112501376764845832724471203 168752065147268749086706805)
        ·
          refine ⟨15820506107556445226878763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168752065147268749086706805 15820506107556445226878763)
          ·
            refine ⟨23730759161334667840318145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15820506107556445226878763 23730759161334667840318145)
            ·
              refine ⟨17798069371001000880238609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23730759161334667840318145 17798069371001000880238609)
              ·
                refine ⟨13348552028250750660178957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17798069371001000880238609 13348552028250750660178957)
                ·
                  refine ⟨5005707010594031497567109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13348552028250750660178957 5005707010594031497567109)
                  ·
                    refine ⟨938570064486380905793833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005707010594031497567109 938570064486380905793833)
                    ·
                      rfl

theorem cell23_5483576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_5483576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483576 prefixEnd_5483576 := by exact prefixLift 5483576
  have htrace : WordTrace (prefixWord ++ tailWord_5483576) baseStart_5483576 baseEnd_5483576 := by
    simpa [prefixWord, tailWord_5483576, baseEnd_5483576] using wordTrace_append hprefix tailTrace_5483576
  have hstable : (prefixWord ++ tailWord_5483576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483576).length < 2 ^ (prefixWord ++ tailWord_5483576).sum := by decide
  have hdescent : baseEnd_5483576 < baseStart_5483576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483619 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 3, 5]
def baseStart_5483619 : Nat := 118140960795 + 5483619 * 2 ^ 59
def prefixEnd_5483619 : Nat := 4983230072969 + 3 ^ 40 * 5483619 * 2
def baseEnd_5483619 : Nat := 938577424375762016381267

theorem tailTrace_5483619 : CollatzResearch.WordTrace tailWord_5483619 prefixEnd_5483619 938577424375762016381267 := by
  unfold tailWord_5483619
  simp only [CollatzResearch.WordTrace]
  refine ⟨200004015920792365409541911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133336010613861576939694607 200004015920792365409541911)
  ·
    refine ⟨300006023881188548114312867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200004015920792365409541911 300006023881188548114312867)
    ·
      refine ⟨450009035821782822171469301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300006023881188548114312867 450009035821782822171469301)
      ·
        refine ⟨42188347108292139578575247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 450009035821782822171469301 42188347108292139578575247)
        ·
          refine ⟨63282520662438209367862871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42188347108292139578575247 63282520662438209367862871)
          ·
            refine ⟨94923780993657314051794307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63282520662438209367862871 94923780993657314051794307)
            ·
              refine ⟨142385671490485971077691461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94923780993657314051794307 142385671490485971077691461)
              ·
                refine ⟨26697313404466119577067149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142385671490485971077691461 26697313404466119577067149)
                ·
                  refine ⟨10011492526674794841400181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26697313404466119577067149 10011492526674794841400181)
                  ·
                    refine ⟨938577424375762016381267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10011492526674794841400181 938577424375762016381267)
                    ·
                      rfl

theorem cell23_5483619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 5].length) (baseStart_5483619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483619 prefixEnd_5483619 := by exact prefixLift 5483619
  have htrace : WordTrace (prefixWord ++ tailWord_5483619) baseStart_5483619 baseEnd_5483619 := by
    simpa [prefixWord, tailWord_5483619, baseEnd_5483619] using wordTrace_append hprefix tailTrace_5483619
  have hstable : (prefixWord ++ tailWord_5483619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483619).length < 2 ^ (prefixWord ++ tailWord_5483619).sum := by decide
  have hdescent : baseEnd_5483619 < baseStart_5483619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483623 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 6]
def baseStart_5483623 : Nat := 118140960795 + 5483623 * 2 ^ 59
def prefixEnd_5483623 : Nat := 4983230072969 + 3 ^ 40 * 5483623 * 2
def baseEnd_5483623 : Nat := 312859369672211559277087

theorem tailTrace_5483623 : CollatzResearch.WordTrace tailWord_5483623 prefixEnd_5483623 312859369672211559277087 := by
  unfold tailWord_5483623
  simp only [CollatzResearch.WordTrace]
  refine ⟨200004161812777874092687523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133336107875185249395125015 200004161812777874092687523)
  ·
    refine ⟨300006242719166811139031285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200004161812777874092687523 300006242719166811139031285)
    ·
      refine ⟨28125585254921888544284183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 300006242719166811139031285 28125585254921888544284183)
      ·
        refine ⟨42188377882382832816426275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28125585254921888544284183 42188377882382832816426275)
        ·
          refine ⟨63282566823574249224639413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42188377882382832816426275 63282566823574249224639413)
          ·
            refine ⟨5932740639710085864809945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63282566823574249224639413 5932740639710085864809945)
            ·
              refine ⟨4449555479782564398607459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5932740639710085864809945 4449555479782564398607459)
              ·
                refine ⟨6674333219673846597911189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449555479782564398607459 6674333219673846597911189)
                ·
                  refine ⟨312859369672211559277087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6674333219673846597911189 312859369672211559277087)
                  ·
                    rfl

theorem cell23_5483623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 6].length) (baseStart_5483623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483623 prefixEnd_5483623 := by exact prefixLift 5483623
  have htrace : WordTrace (prefixWord ++ tailWord_5483623) baseStart_5483623 baseEnd_5483623 := by
    simpa [prefixWord, tailWord_5483623, baseEnd_5483623] using wordTrace_append hprefix tailTrace_5483623
  have hstable : (prefixWord ++ tailWord_5483623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483623).length < 2 ^ (prefixWord ++ tailWord_5483623).sum := by decide
  have hdescent : baseEnd_5483623 < baseStart_5483623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483669 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_5483669 : Nat := 118140960795 + 5483669 * 2 ^ 59
def prefixEnd_5483669 : Nat := 4983230072969 + 3 ^ 40 * 5483669 * 2
def baseEnd_5483669 : Nat := 2815757947160010853518571

theorem tailTrace_5483669 : CollatzResearch.WordTrace tailWord_5483669 prefixEnd_5483669 2815757947160010853518571 := by
  unfold tailWord_5483669
  simp only [CollatzResearch.WordTrace]
  refine ⟨200005839570611223948862061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133337226380407482632574707 200005839570611223948862061)
  ·
    refine ⟨75002189838979208980823273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200005839570611223948862061 75002189838979208980823273)
    ·
      refine ⟨56251642379234406735617455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75002189838979208980823273 56251642379234406735617455)
      ·
        refine ⟨84377463568851610103426183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56251642379234406735617455 84377463568851610103426183)
        ·
          refine ⟨126566195353277415155139275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84377463568851610103426183 126566195353277415155139275)
          ·
            refine ⟨189849293029916122732708913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126566195353277415155139275 189849293029916122732708913)
            ·
              refine ⟨142386969772437092049531685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189849293029916122732708913 142386969772437092049531685)
              ·
                refine ⟨26697556832331954759287191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142386969772437092049531685 26697556832331954759287191)
                ·
                  refine ⟨40046335248497932138930787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26697556832331954759287191 40046335248497932138930787)
                  ·
                    refine ⟨60069502872746898208396181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40046335248497932138930787 60069502872746898208396181)
                    ·
                      refine ⟨2815757947160010853518571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60069502872746898208396181 2815757947160010853518571)
                      ·
                        rfl

theorem cell23_5483669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_5483669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483669 prefixEnd_5483669 := by exact prefixLift 5483669
  have htrace : WordTrace (prefixWord ++ tailWord_5483669) baseStart_5483669 baseEnd_5483669 := by
    simpa [prefixWord, tailWord_5483669, baseEnd_5483669] using wordTrace_append hprefix tailTrace_5483669
  have hstable : (prefixWord ++ tailWord_5483669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483669).length < 2 ^ (prefixWord ++ tailWord_5483669).sum := by decide
  have hdescent : baseEnd_5483669 < baseStart_5483669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483710 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_5483710 : Nat := 118140960795 + 5483710 * 2 ^ 59
def prefixEnd_5483710 : Nat := 4983230072969 + 3 ^ 40 * 5483710 * 2
def baseEnd_5483710 : Nat := 2815778999866845193105883

theorem tailTrace_5483710 : CollatzResearch.WordTrace tailWord_5483710 prefixEnd_5483710 2815778999866845193105883 := by
  unfold tailWord_5483710
  simp only [CollatzResearch.WordTrace]
  refine ⟨25000916870432835993888073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133338223308975125300736389 25000916870432835993888073)
  ·
    refine ⟨18750687652824626995416055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25000916870432835993888073 18750687652824626995416055)
    ·
      refine ⟨28126031479236940493124083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18750687652824626995416055 28126031479236940493124083)
      ·
        refine ⟨42189047218855410739686125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28126031479236940493124083 42189047218855410739686125)
        ·
          refine ⟨15820892707070779027382297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42189047218855410739686125 15820892707070779027382297)
          ·
            refine ⟨11865669530303084270536723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15820892707070779027382297 11865669530303084270536723)
            ·
              refine ⟨17798504295454626405805085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865669530303084270536723 17798504295454626405805085)
              ·
                refine ⟨6674439110795484902176907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17798504295454626405805085 6674439110795484902176907)
                ·
                  refine ⟨10011658666193227353265361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674439110795484902176907 10011658666193227353265361)
                  ·
                    refine ⟨7508743999644920514949021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10011658666193227353265361 7508743999644920514949021)
                    ·
                      refine ⟨2815778999866845193105883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7508743999644920514949021 2815778999866845193105883)
                      ·
                        rfl

theorem cell23_5483710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_5483710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483710 prefixEnd_5483710 := by exact prefixLift 5483710
  have htrace : WordTrace (prefixWord ++ tailWord_5483710) baseStart_5483710 baseEnd_5483710 := by
    simpa [prefixWord, tailWord_5483710, baseEnd_5483710] using wordTrace_append hprefix tailTrace_5483710
  have hstable : (prefixWord ++ tailWord_5483710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483710).length < 2 ^ (prefixWord ++ tailWord_5483710).sum := by decide
  have hdescent : baseEnd_5483710 < baseStart_5483710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483723 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 3]
def baseStart_5483723 : Nat := 118140960795 + 5483723 * 2 ^ 59
def prefixEnd_5483723 : Nat := 4983230072969 + 3 ^ 40 * 5483723 * 2
def baseEnd_5483723 : Nat := 2815785675115353642243323

theorem tailTrace_5483723 : CollatzResearch.WordTrace tailWord_5483723 prefixEnd_5483723 2815785675115353642243323 := by
  unfold tailWord_5483723
  simp only [CollatzResearch.WordTrace]
  refine ⟨200007809112415591171327823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133338539408277060780885215 200007809112415591171327823)
  ·
    refine ⟨300011713668623386756991735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200007809112415591171327823 300011713668623386756991735)
    ·
      refine ⟨450017570502935080135487603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300011713668623386756991735 450017570502935080135487603)
      ·
        refine ⟨675026355754402620203231405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450017570502935080135487603 675026355754402620203231405)
        ·
          refine ⟨253134883407900982576211777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 675026355754402620203231405 253134883407900982576211777)
          ·
            refine ⟨189851162555925736932158833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253134883407900982576211777 189851162555925736932158833)
            ·
              refine ⟨142388371916944302699119125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189851162555925736932158833 142388371916944302699119125)
              ·
                refine ⟨6674454933606764189021209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142388371916944302699119125 6674454933606764189021209)
                ·
                  refine ⟨5005841200205073141765907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674454933606764189021209 5005841200205073141765907)
                  ·
                    refine ⟨7508761800307609712648861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5005841200205073141765907 7508761800307609712648861)
                    ·
                      refine ⟨2815785675115353642243323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7508761800307609712648861 2815785675115353642243323)
                      ·
                        rfl

theorem cell23_5483723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 1, 3].length) (baseStart_5483723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483723 prefixEnd_5483723 := by exact prefixLift 5483723
  have htrace : WordTrace (prefixWord ++ tailWord_5483723) baseStart_5483723 baseEnd_5483723 := by
    simpa [prefixWord, tailWord_5483723, baseEnd_5483723] using wordTrace_append hprefix tailTrace_5483723
  have hstable : (prefixWord ++ tailWord_5483723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483723).length < 2 ^ (prefixWord ++ tailWord_5483723).sum := by decide
  have hdescent : baseEnd_5483723 < baseStart_5483723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483734 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5483734 : Nat := 118140960795 + 5483734 * 2 ^ 59
def prefixEnd_5483734 : Nat := 4983230072969 + 3 ^ 40 * 5483734 * 2
def baseEnd_5483734 : Nat := 938597107800851033068591

theorem tailTrace_5483734 : CollatzResearch.WordTrace tailWord_5483734 prefixEnd_5483734 938597107800851033068591 := by
  unfold tailWord_5483734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12500513144710983753123641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133338806876917160033318837 12500513144710983753123641)
  ·
    refine ⟨9375384858533237814842731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12500513144710983753123641 9375384858533237814842731)
    ·
      refine ⟨14063077287799856722264097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9375384858533237814842731 14063077287799856722264097)
      ·
        refine ⟨10547307965849892541698073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14063077287799856722264097 10547307965849892541698073)
        ·
          refine ⟨7910480974387419406273555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10547307965849892541698073 7910480974387419406273555)
          ·
            refine ⟨11865721461581129109410333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910480974387419406273555 11865721461581129109410333)
            ·
              refine ⟨4449645548092923416028875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11865721461581129109410333 4449645548092923416028875)
              ·
                refine ⟨6674468322139385124043313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449645548092923416028875 6674468322139385124043313)
                ·
                  refine ⟨5005851241604538843032485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674468322139385124043313 5005851241604538843032485)
                  ·
                    refine ⟨938597107800851033068591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005851241604538843032485 938597107800851033068591)
                    ·
                      rfl

theorem cell23_5483734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5483734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483734 prefixEnd_5483734 := by exact prefixLift 5483734
  have htrace : WordTrace (prefixWord ++ tailWord_5483734) baseStart_5483734 baseEnd_5483734 := by
    simpa [prefixWord, tailWord_5483734, baseEnd_5483734] using wordTrace_append hprefix tailTrace_5483734
  have hstable : (prefixWord ++ tailWord_5483734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483734).length < 2 ^ (prefixWord ++ tailWord_5483734).sum := by decide
  have hdescent : baseEnd_5483734 < baseStart_5483734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483739 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 6, 6]
def baseStart_5483739 : Nat := 118140960795 + 5483739 * 2 ^ 59
def prefixEnd_5483739 : Nat := 4983230072969 + 3 ^ 40 * 5483739 * 2
def baseEnd_5483739 : Nat := 938597963601941859881083

theorem tailTrace_5483739 : CollatzResearch.WordTrace tailWord_5483739 prefixEnd_5483739 938597963601941859881083 := by
  unfold tailWord_5483739
  simp only [CollatzResearch.WordTrace]
  refine ⟨200008392680357625903910271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133338928453571750602606847 200008392680357625903910271)
  ·
    refine ⟨300012589020536438855865407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200008392680357625903910271 300012589020536438855865407)
    ·
      refine ⟨450018883530804658283798111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300012589020536438855865407 450018883530804658283798111)
      ·
        refine ⟨675028325296206987425697167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450018883530804658283798111 675028325296206987425697167)
        ·
          refine ⟨1012542487944310481138545751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675028325296206987425697167 1012542487944310481138545751)
          ·
            refine ⟨1518813731916465721707818627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012542487944310481138545751 1518813731916465721707818627)
            ·
              refine ⟨2278220597874698582561727941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518813731916465721707818627 2278220597874698582561727941)
              ·
                refine ⟨427166362101505984230323989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2278220597874698582561727941 427166362101505984230323989)
                ·
                  refine ⟨20023423223508093010796437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 427166362101505984230323989 20023423223508093010796437)
                  ·
                    refine ⟨938597963601941859881083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20023423223508093010796437 938597963601941859881083)
                    ·
                      rfl

theorem cell23_5483739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 6].length) (baseStart_5483739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483739 prefixEnd_5483739 := by exact prefixLift 5483739
  have htrace : WordTrace (prefixWord ++ tailWord_5483739) baseStart_5483739 baseEnd_5483739 := by
    simpa [prefixWord, tailWord_5483739, baseEnd_5483739] using wordTrace_append hprefix tailTrace_5483739
  have hstable : (prefixWord ++ tailWord_5483739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483739).length < 2 ^ (prefixWord ++ tailWord_5483739).sum := by decide
  have hdescent : baseEnd_5483739 < baseStart_5483739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483837 : List Nat := [1, 4, 1, 5, 1, 1, 1, 4, 5]
def baseStart_5483837 : Nat := 118140960795 + 5483837 * 2 ^ 59
def prefixEnd_5483837 : Nat := 4983230072969 + 3 ^ 40 * 5483837 * 2
def baseEnd_5483837 : Nat := 312871579101107355135311

theorem tailTrace_5483837 : CollatzResearch.WordTrace tailWord_5483837 prefixEnd_5483837 312871579101107355135311 := by
  unfold tailWord_5483837
  simp only [CollatzResearch.WordTrace]
  refine ⟨200011967034002588640977765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133341311356001725760651843 200011967034002588640977765)
  ·
    refine ⟨37502243818875485370183331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200011967034002588640977765 37502243818875485370183331)
    ·
      refine ⟨56253365728313228055274997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37502243818875485370183331 56253365728313228055274997)
      ·
        refine ⟨5273753037029365130182031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56253365728313228055274997 5273753037029365130182031)
        ·
          refine ⟨7910629555544047695273047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273753037029365130182031 7910629555544047695273047)
          ·
            refine ⟨11865944333316071542909571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910629555544047695273047 11865944333316071542909571)
            ·
              refine ⟨17798916499974107314364357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865944333316071542909571 17798916499974107314364357)
              ·
                refine ⟨3337296843745145121443317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17798916499974107314364357 3337296843745145121443317)
                ·
                  refine ⟨312871579101107355135311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3337296843745145121443317 312871579101107355135311)
                  ·
                    rfl

theorem cell23_5483837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_5483837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483837 prefixEnd_5483837 := by exact prefixLift 5483837
  have htrace : WordTrace (prefixWord ++ tailWord_5483837) baseStart_5483837 baseEnd_5483837 := by
    simpa [prefixWord, tailWord_5483837, baseEnd_5483837] using wordTrace_append hprefix tailTrace_5483837
  have hstable : (prefixWord ++ tailWord_5483837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483837).length < 2 ^ (prefixWord ++ tailWord_5483837).sum := by decide
  have hdescent : baseEnd_5483837 < baseStart_5483837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483863 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 5, 4]
def baseStart_5483863 : Nat := 118140960795 + 5483863 * 2 ^ 59
def prefixEnd_5483863 : Nat := 4983230072969 + 3 ^ 40 * 5483863 * 2
def baseEnd_5483863 : Nat := 938619187468994364830893

theorem tailTrace_5483863 : CollatzResearch.WordTrace tailWord_5483863 prefixEnd_5483863 938619187468994364830893 := by
  unfold tailWord_5483863
  simp only [CollatzResearch.WordTrace]
  refine ⟨200012915331908395081424243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133341943554605596720949495 200012915331908395081424243)
  ·
    refine ⟨300019372997862592622136365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200012915331908395081424243 300019372997862592622136365)
    ·
      refine ⟨112507264874198472233301137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300019372997862592622136365 112507264874198472233301137)
      ·
        refine ⟨84380448655648854174975853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112507264874198472233301137 84380448655648854174975853)
        ·
          refine ⟨31642668245868320315615945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84380448655648854174975853 31642668245868320315615945)
          ·
            refine ⟨23732001184401240236711959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31642668245868320315615945 23732001184401240236711959)
            ·
              refine ⟨35598001776601860355067939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23732001184401240236711959 35598001776601860355067939)
              ·
                refine ⟨53397002664902790532601909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35598001776601860355067939 53397002664902790532601909)
                ·
                  refine ⟨5005968999834636612431429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53397002664902790532601909 5005968999834636612431429)
                  ·
                    refine ⟨938619187468994364830893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005968999834636612431429 938619187468994364830893)
                    ·
                      rfl

theorem cell23_5483863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_5483863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483863 prefixEnd_5483863 := by exact prefixLift 5483863
  have htrace : WordTrace (prefixWord ++ tailWord_5483863) baseStart_5483863 baseEnd_5483863 := by
    simpa [prefixWord, tailWord_5483863, baseEnd_5483863] using wordTrace_append hprefix tailTrace_5483863
  have hstable : (prefixWord ++ tailWord_5483863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483863).length < 2 ^ (prefixWord ++ tailWord_5483863).sum := by decide
  have hdescent : baseEnd_5483863 < baseStart_5483863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483930 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2]
def baseStart_5483930 : Nat := 118140960795 + 5483930 * 2 ^ 59
def prefixEnd_5483930 : Nat := 4983230072969 + 3 ^ 40 * 5483930 * 2
def baseEnd_5483930 : Nat := 2815891965610834332354871

theorem tailTrace_5483930 : CollatzResearch.WordTrace tailWord_5483930 prefixEnd_5483930 2815891965610834332354871 := by
  unfold tailWord_5483930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50003839755666416381028311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133343572681777110349408829 50003839755666416381028311)
  ·
    refine ⟨75005759633499624571542467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50003839755666416381028311 75005759633499624571542467)
    ·
      refine ⟨112508639450249436857313701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75005759633499624571542467 112508639450249436857313701)
      ·
        refine ⟨21095369896921769410746319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112508639450249436857313701 21095369896921769410746319)
        ·
          refine ⟨31643054845382654116119479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21095369896921769410746319 31643054845382654116119479)
          ·
            refine ⟨47464582268073981174179219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31643054845382654116119479 47464582268073981174179219)
            ·
              refine ⟨71196873402110971761268829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47464582268073981174179219 71196873402110971761268829)
              ·
                refine ⟨26698827525791614410475811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71196873402110971761268829 26698827525791614410475811)
                ·
                  refine ⟨40048241288687421615713717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26698827525791614410475811 40048241288687421615713717)
                  ·
                    refine ⟨3754522620814445776473161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40048241288687421615713717 3754522620814445776473161)
                    ·
                      refine ⟨2815891965610834332354871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754522620814445776473161 2815891965610834332354871)
                      ·
                        rfl

theorem cell23_5483930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_5483930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483930 prefixEnd_5483930 := by exact prefixLift 5483930
  have htrace : WordTrace (prefixWord ++ tailWord_5483930) baseStart_5483930 baseEnd_5483930 := by
    simpa [prefixWord, tailWord_5483930, baseEnd_5483930] using wordTrace_append hprefix tailTrace_5483930
  have hstable : (prefixWord ++ tailWord_5483930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483930).length < 2 ^ (prefixWord ++ tailWord_5483930).sum := by decide
  have hdescent : baseEnd_5483930 < baseStart_5483930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5483997 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_5483997 : Nat := 118140960795 + 5483997 * 2 ^ 59
def prefixEnd_5483997 : Nat := 4983230072969 + 3 ^ 40 * 5483997 * 2
def baseEnd_5483997 : Nat := 2815926368814685570217063

theorem tailTrace_5483997 : CollatzResearch.WordTrace tailWord_5483997 prefixEnd_5483997 2815926368814685570217063 := by
  unfold tailWord_5483997
  simp only [CollatzResearch.WordTrace]
  refine ⟨200017802713422935966802245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133345201808948623977868163 200017802713422935966802245)
  ·
    refine ⟨37503338008766800493775421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200017802713422935966802245 37503338008766800493775421)
    ·
      refine ⟨14063751753287550185165783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37503338008766800493775421 14063751753287550185165783)
      ·
        refine ⟨21095627629931325277748675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14063751753287550185165783 21095627629931325277748675)
        ·
          refine ⟨31643441444896987916623013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21095627629931325277748675 31643441444896987916623013)
          ·
            refine ⟨5933145270918185234366815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31643441444896987916623013 5933145270918185234366815)
            ·
              refine ⟨8899717906377277851550223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933145270918185234366815 8899717906377277851550223)
              ·
                refine ⟨13349576859565916777325335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8899717906377277851550223 13349576859565916777325335)
                ·
                  refine ⟨20024365289348875165988003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13349576859565916777325335 20024365289348875165988003)
                  ·
                    refine ⟨30036547934023312748982005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20024365289348875165988003 30036547934023312748982005)
                    ·
                      refine ⟨2815926368814685570217063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30036547934023312748982005 2815926368814685570217063)
                      ·
                        rfl

theorem cell23_5483997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_5483997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5483997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5483997 prefixEnd_5483997 := by exact prefixLift 5483997
  have htrace : WordTrace (prefixWord ++ tailWord_5483997) baseStart_5483997 baseEnd_5483997 := by
    simpa [prefixWord, tailWord_5483997, baseEnd_5483997] using wordTrace_append hprefix tailTrace_5483997
  have hstable : (prefixWord ++ tailWord_5483997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5483997).length < 2 ^ (prefixWord ++ tailWord_5483997).sum := by decide
  have hdescent : baseEnd_5483997 < baseStart_5483997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5483997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484037 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 1, 3, 2]
def baseStart_5484037 : Nat := 118140960795 + 5484037 * 2 ^ 59
def prefixEnd_5484037 : Nat := 4983230072969 + 3 ^ 40 * 5484037 * 2
def baseEnd_5484037 : Nat := 2815946908040865413716879

theorem tailTrace_5484037 : CollatzResearch.WordTrace tailWord_5484037 prefixEnd_5484037 2815946908040865413716879 := by
  unfold tailWord_5484037
  simp only [CollatzResearch.WordTrace]
  refine ⟨200019261633278022798258365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133346174422185348532172243 200019261633278022798258365)
  ·
    refine ⟨75007223112479258549346887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200019261633278022798258365 75007223112479258549346887)
    ·
      refine ⟨112510834668718887824020331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75007223112479258549346887 112510834668718887824020331)
      ·
        refine ⟨168766252003078331736030497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112510834668718887824020331 168766252003078331736030497)
        ·
          refine ⟨126574689002308748802022873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168766252003078331736030497 126574689002308748802022873)
          ·
            refine ⟨94931016751731561601517155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126574689002308748802022873 94931016751731561601517155)
            ·
              refine ⟨142396525127597342402275733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94931016751731561601517155 142396525127597342402275733)
              ·
                refine ⟨6674837115356125425106675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142396525127597342402275733 6674837115356125425106675)
                ·
                  refine ⟨10012255673034188137660013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674837115356125425106675 10012255673034188137660013)
                  ·
                    refine ⟨3754595877387820551622505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10012255673034188137660013 3754595877387820551622505)
                    ·
                      refine ⟨2815946908040865413716879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754595877387820551622505 2815946908040865413716879)
                      ·
                        rfl

theorem cell23_5484037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_5484037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484037 prefixEnd_5484037 := by exact prefixLift 5484037
  have htrace : WordTrace (prefixWord ++ tailWord_5484037) baseStart_5484037 baseEnd_5484037 := by
    simpa [prefixWord, tailWord_5484037, baseEnd_5484037] using wordTrace_append hprefix tailTrace_5484037
  have hstable : (prefixWord ++ tailWord_5484037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484037).length < 2 ^ (prefixWord ++ tailWord_5484037).sum := by decide
  have hdescent : baseEnd_5484037 < baseStart_5484037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484045 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5484045 : Nat := 118140960795 + 5484045 * 2 ^ 59
def prefixEnd_5484045 : Nat := 4983230072969 + 3 ^ 40 * 5484045 * 2
def baseEnd_5484045 : Nat := 2815951015886101382416843

theorem tailTrace_5484045 : CollatzResearch.WordTrace tailWord_5484045 prefixEnd_5484045 2815951015886101382416843 := by
  unfold tailWord_5484045
  simp only [CollatzResearch.WordTrace]
  refine ⟨200019553417249040164549589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133346368944832693443033059 200019553417249040164549589)
  ·
    refine ⟨4687958283216774378856631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 200019553417249040164549589 4687958283216774378856631)
    ·
      refine ⟨7031937424825161568284947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687958283216774378856631 7031937424825161568284947)
      ·
        refine ⟨10547906137237742352427421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7031937424825161568284947 10547906137237742352427421)
        ·
          refine ⟨3955464801464153382160283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10547906137237742352427421 3955464801464153382160283)
          ·
            refine ⟨5933197202196230073240425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955464801464153382160283 5933197202196230073240425)
            ·
              refine ⟨4449897901647172554930319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5933197202196230073240425 4449897901647172554930319)
              ·
                refine ⟨6674846852470758832395479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4449897901647172554930319 6674846852470758832395479)
                ·
                  refine ⟨10012270278706138248593219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674846852470758832395479 10012270278706138248593219)
                  ·
                    refine ⟨15018405418059207372889829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10012270278706138248593219 15018405418059207372889829)
                    ·
                      refine ⟨2815951015886101382416843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15018405418059207372889829 2815951015886101382416843)
                      ·
                        rfl

theorem cell23_5484045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5484045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484045 prefixEnd_5484045 := by exact prefixLift 5484045
  have htrace : WordTrace (prefixWord ++ tailWord_5484045) baseStart_5484045 baseEnd_5484045 := by
    simpa [prefixWord, tailWord_5484045, baseEnd_5484045] using wordTrace_append hprefix tailTrace_5484045
  have hstable : (prefixWord ++ tailWord_5484045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484045).length < 2 ^ (prefixWord ++ tailWord_5484045).sum := by decide
  have hdescent : baseEnd_5484045 < baseStart_5484045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484140 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 4]
def baseStart_5484140 : Nat := 118140960795 + 5484140 * 2 ^ 59
def prefixEnd_5484140 : Nat := 4983230072969 + 3 ^ 40 * 5484140 * 2
def baseEnd_5484140 : Nat := 2815999796548278510728905

theorem tailTrace_5484140 : CollatzResearch.WordTrace tailWord_5484140 prefixEnd_5484140 2815999796548278510728905 := by
  unfold tailWord_5484140
  simp only [CollatzResearch.WordTrace]
  refine ⟨100011509175952435694628937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133348678901269914259505249 100011509175952435694628937)
  ·
    refine ⟨75008631881964326770971703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100011509175952435694628937 75008631881964326770971703)
    ·
      refine ⟨112512947822946490156457555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75008631881964326770971703 112512947822946490156457555)
      ·
        refine ⟨168769421734419735234686333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112512947822946490156457555 168769421734419735234686333)
        ·
          refine ⟨63288533150407400713007375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168769421734419735234686333 63288533150407400713007375)
          ·
            refine ⟨94932799725611101069511063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63288533150407400713007375 94932799725611101069511063)
            ·
              refine ⟨142399199588416651604266595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94932799725611101069511063 142399199588416651604266595)
              ·
                refine ⟨213598799382624977406399893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142399199588416651604266595 213598799382624977406399893)
                ·
                  refine ⟨10012443721060545815924995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 213598799382624977406399893 10012443721060545815924995)
                  ·
                    refine ⟨15018665581590818723887493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10012443721060545815924995 15018665581590818723887493)
                    ·
                      refine ⟨2815999796548278510728905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15018665581590818723887493 2815999796548278510728905)
                      ·
                        rfl

theorem cell23_5484140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_5484140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484140 prefixEnd_5484140 := by exact prefixLift 5484140
  have htrace : WordTrace (prefixWord ++ tailWord_5484140) baseStart_5484140 baseEnd_5484140 := by
    simpa [prefixWord, tailWord_5484140, baseEnd_5484140] using wordTrace_append hprefix tailTrace_5484140
  have hstable : (prefixWord ++ tailWord_5484140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484140).length < 2 ^ (prefixWord ++ tailWord_5484140).sum := by decide
  have hdescent : baseEnd_5484140 < baseStart_5484140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484157 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_5484157 : Nat := 118140960795 + 5484157 * 2 ^ 59
def prefixEnd_5484157 : Nat := 4983230072969 + 3 ^ 40 * 5484157 * 2
def baseEnd_5484157 : Nat := 2816008525719404944216327

theorem tailTrace_5484157 : CollatzResearch.WordTrace tailWord_5484157 prefixEnd_5484157 2816008525719404944216327 := by
  unfold tailWord_5484157
  simp only [CollatzResearch.WordTrace]
  refine ⟨200023638392843283292626725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133349092261895522195084483 200023638392843283292626725)
  ·
    refine ⟨37504432198658115617367511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200023638392843283292626725 37504432198658115617367511)
    ·
      refine ⟨56256648297987173426051267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37504432198658115617367511 56256648297987173426051267)
      ·
        refine ⟨84384972446980760139076901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56256648297987173426051267 84384972446980760139076901)
        ·
          refine ⟨15822182333808892526076919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84384972446980760139076901 15822182333808892526076919)
          ·
            refine ⟨23733273500713338789115379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15822182333808892526076919 23733273500713338789115379)
            ·
              refine ⟨35599910251070008183673069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23733273500713338789115379 35599910251070008183673069)
              ·
                refine ⟨13349966344151253068877401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35599910251070008183673069 13349966344151253068877401)
                ·
                  refine ⟨10012474758113439801658051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13349966344151253068877401 10012474758113439801658051)
                  ·
                    refine ⟨15018712137170159702487077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10012474758113439801658051 15018712137170159702487077)
                    ·
                      refine ⟨2816008525719404944216327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15018712137170159702487077 2816008525719404944216327)
                      ·
                        rfl

theorem cell23_5484157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_5484157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484157 prefixEnd_5484157 := by exact prefixLift 5484157
  have htrace : WordTrace (prefixWord ++ tailWord_5484157) baseStart_5484157 baseEnd_5484157 := by
    simpa [prefixWord, tailWord_5484157, baseEnd_5484157] using wordTrace_append hprefix tailTrace_5484157
  have hstable : (prefixWord ++ tailWord_5484157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484157).length < 2 ^ (prefixWord ++ tailWord_5484157).sum := by decide
  have hdescent : baseEnd_5484157 < baseStart_5484157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484191 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5484191 : Nat := 118140960795 + 5484191 * 2 ^ 59
def prefixEnd_5484191 : Nat := 4983230072969 + 3 ^ 40 * 5484191 * 2
def baseEnd_5484191 : Nat := 2816025984061657811191171

theorem tailTrace_5484191 : CollatzResearch.WordTrace tailWord_5484191 prefixEnd_5484191 2816025984061657811191171 := by
  unfold tailWord_5484191
  simp only [CollatzResearch.WordTrace]
  refine ⟨200024878474720107099364427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133349918983146738066242951 200024878474720107099364427)
  ·
    refine ⟨300037317712080160649046641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200024878474720107099364427 300037317712080160649046641)
    ·
      refine ⟨225027988284060120486784981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300037317712080160649046641 225027988284060120486784981)
      ·
        refine ⟨5274093475407659073909023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 225027988284060120486784981 5274093475407659073909023)
        ·
          refine ⟨7911140213111488610863535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5274093475407659073909023 7911140213111488610863535)
          ·
            refine ⟨11866710319667232916295303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7911140213111488610863535 11866710319667232916295303)
            ·
              refine ⟨17800065479500849374442955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11866710319667232916295303 17800065479500849374442955)
              ·
                refine ⟨26700098219251274061664433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17800065479500849374442955 26700098219251274061664433)
                ·
                  refine ⟨20025073664438455546248325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26700098219251274061664433 20025073664438455546248325)
                  ·
                    refine ⟨3754701312082210414921561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20025073664438455546248325 3754701312082210414921561)
                    ·
                      refine ⟨2816025984061657811191171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754701312082210414921561 2816025984061657811191171)
                      ·
                        rfl

theorem cell23_5484191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5484191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484191 prefixEnd_5484191 := by exact prefixLift 5484191
  have htrace : WordTrace (prefixWord ++ tailWord_5484191) baseStart_5484191 baseEnd_5484191 := by
    simpa [prefixWord, tailWord_5484191, baseEnd_5484191] using wordTrace_append hprefix tailTrace_5484191
  have hstable : (prefixWord ++ tailWord_5484191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484191).length < 2 ^ (prefixWord ++ tailWord_5484191).sum := by decide
  have hdescent : baseEnd_5484191 < baseStart_5484191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484241 : List Nat := [1, 2, 2, 1, 2, 4, 2, 4, 1, 1, 3]
def baseStart_5484241 : Nat := 118140960795 + 5484241 * 2 ^ 59
def prefixEnd_5484241 : Nat := 4983230072969 + 3 ^ 40 * 5484241 * 2
def baseEnd_5484241 : Nat := 2816051658094382615565941

theorem tailTrace_5484241 : CollatzResearch.WordTrace tailWord_5484241 prefixEnd_5484241 2816051658094382615565941 := by
  unfold tailWord_5484241
  simp only [CollatzResearch.WordTrace]
  refine ⟨200026702124538965638684577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133351134749692643759123051 200026702124538965638684577)
  ·
    refine ⟨150020026593404224229013433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200026702124538965638684577 150020026593404224229013433)
    ·
      refine ⟨112515019945053168171760075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150020026593404224229013433 112515019945053168171760075)
      ·
        refine ⟨168772529917579752257640113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112515019945053168171760075 168772529917579752257640113)
        ·
          refine ⟨126579397438184814193230085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168772529917579752257640113 126579397438184814193230085)
          ·
            refine ⟨23733637019659652661230641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126579397438184814193230085 23733637019659652661230641)
            ·
              refine ⟨17800227764744739495922981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23733637019659652661230641 17800227764744739495922981)
              ·
                refine ⟨3337542705889638655485559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17800227764744739495922981 3337542705889638655485559)
                ·
                  refine ⟨5006314058834457983228339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337542705889638655485559 5006314058834457983228339)
                  ·
                    refine ⟨7509471088251686974842509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5006314058834457983228339 7509471088251686974842509)
                    ·
                      refine ⟨2816051658094382615565941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7509471088251686974842509 2816051658094382615565941)
                      ·
                        rfl

theorem cell23_5484241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 1, 3].length) (baseStart_5484241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484241 prefixEnd_5484241 := by exact prefixLift 5484241
  have htrace : WordTrace (prefixWord ++ tailWord_5484241) baseStart_5484241 baseEnd_5484241 := by
    simpa [prefixWord, tailWord_5484241, baseEnd_5484241] using wordTrace_append hprefix tailTrace_5484241
  have hstable : (prefixWord ++ tailWord_5484241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484241).length < 2 ^ (prefixWord ++ tailWord_5484241).sum := by decide
  have hdescent : baseEnd_5484241 < baseStart_5484241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484264 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_5484264 : Nat := 118140960795 + 5484264 * 2 ^ 59
def prefixEnd_5484264 : Nat := 4983230072969 + 3 ^ 40 * 5484264 * 2
def baseEnd_5484264 : Nat := 2816063468149436025578335

theorem tailTrace_5484264 : CollatzResearch.WordTrace tailWord_5484264 prefixEnd_5484264 2816063468149436025578335 := by
  unfold tailWord_5484264
  simp only [CollatzResearch.WordTrace]
  refine ⟨100013770501727820283385923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133351694002303760377847897 100013770501727820283385923)
  ·
    refine ⟨150020655752591730425078885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100013770501727820283385923 150020655752591730425078885)
    ·
      refine ⟨28128872953610949454702291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150020655752591730425078885 28128872953610949454702291)
      ·
        refine ⟨42193309430416424182053437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28128872953610949454702291 42193309430416424182053437)
        ·
          refine ⟨15822491036406159068270039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42193309430416424182053437 15822491036406159068270039)
          ·
            refine ⟨23733736554609238602405059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15822491036406159068270039 23733736554609238602405059)
            ·
              refine ⟨35600604831913857903607589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23733736554609238602405059 35600604831913857903607589)
              ·
                refine ⟨6675113405983848356926423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35600604831913857903607589 6675113405983848356926423)
                ·
                  refine ⟨10012670108975772535389635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675113405983848356926423 10012670108975772535389635)
                  ·
                    refine ⟨15019005163463658803084453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10012670108975772535389635 15019005163463658803084453)
                    ·
                      refine ⟨2816063468149436025578335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15019005163463658803084453 2816063468149436025578335)
                      ·
                        rfl

theorem cell23_5484264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_5484264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484264 prefixEnd_5484264 := by exact prefixLift 5484264
  have htrace : WordTrace (prefixWord ++ tailWord_5484264) baseStart_5484264 baseEnd_5484264 := by
    simpa [prefixWord, tailWord_5484264, baseEnd_5484264] using wordTrace_append hprefix tailTrace_5484264
  have hstable : (prefixWord ++ tailWord_5484264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484264).length < 2 ^ (prefixWord ++ tailWord_5484264).sum := by decide
  have hdescent : baseEnd_5484264 < baseStart_5484264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484267 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 3]
def baseStart_5484267 : Nat := 118140960795 + 5484267 * 2 ^ 59
def prefixEnd_5484267 : Nat := 4983230072969 + 3 ^ 40 * 5484267 * 2
def baseEnd_5484267 : Nat := 2816065008591399513840821

theorem tailTrace_5484267 : CollatzResearch.WordTrace tailWord_5484267 prefixEnd_5484267 2816065008591399513840821 := by
  unfold tailWord_5484267
  simp only [CollatzResearch.WordTrace]
  refine ⟨200027650422444772079131055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133351766948296514719420703 200027650422444772079131055)
  ·
    refine ⟨300041475633667158118696583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200027650422444772079131055 300041475633667158118696583)
    ·
      refine ⟨450062213450500737178044875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300041475633667158118696583 450062213450500737178044875)
      ·
        refine ⟨675093320175751105767067313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450062213450500737178044875 675093320175751105767067313)
        ·
          refine ⟨506319990131813329325300485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675093320175751105767067313 506319990131813329325300485)
          ·
            refine ⟨94934998149714999248493841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 506319990131813329325300485 94934998149714999248493841)
            ·
              refine ⟨71201248612286249436370381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94934998149714999248493841 71201248612286249436370381)
              ·
                refine ⟨26700468229607343538638893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71201248612286249436370381 26700468229607343538638893)
                ·
                  refine ⟨10012675586102753826989585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26700468229607343538638893 10012675586102753826989585)
                  ·
                    refine ⟨7509506689577065370242189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10012675586102753826989585 7509506689577065370242189)
                    ·
                      refine ⟨2816065008591399513840821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7509506689577065370242189 2816065008591399513840821)
                      ·
                        rfl

theorem cell23_5484267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 3].length) (baseStart_5484267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484267 prefixEnd_5484267 := by exact prefixLift 5484267
  have htrace : WordTrace (prefixWord ++ tailWord_5484267) baseStart_5484267 baseEnd_5484267 := by
    simpa [prefixWord, tailWord_5484267, baseEnd_5484267] using wordTrace_append hprefix tailTrace_5484267
  have hstable : (prefixWord ++ tailWord_5484267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484267).length < 2 ^ (prefixWord ++ tailWord_5484267).sum := by decide
  have hdescent : baseEnd_5484267 < baseStart_5484267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484284 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_5484284 : Nat := 118140960795 + 5484284 * 2 ^ 59
def prefixEnd_5484284 : Nat := 4983230072969 + 3 ^ 40 * 5484284 * 2
def baseEnd_5484284 : Nat := 2816073737762525947328243

theorem tailTrace_5484284 : CollatzResearch.WordTrace tailWord_5484284 prefixEnd_5484284 2816073737762525947328243 := by
  unfold tailWord_5484284
  simp only [CollatzResearch.WordTrace]
  refine ⟨100014135231691591991249953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133352180308922122654999937 100014135231691591991249953)
  ·
    refine ⟨75010601423768693993437465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100014135231691591991249953 75010601423768693993437465)
    ·
      refine ⟨56257951067826520495078099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75010601423768693993437465 56257951067826520495078099)
      ·
        refine ⟨84386926601739780742617149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56257951067826520495078099 84386926601739780742617149)
        ·
          refine ⟨31645097475652417778481431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84386926601739780742617149 31645097475652417778481431)
          ·
            refine ⟨47467646213478626667722147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31645097475652417778481431 47467646213478626667722147)
            ·
              refine ⟨71201469320217940001583221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47467646213478626667722147 71201469320217940001583221)
              ·
                refine ⟨6675137748770431875148427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71201469320217940001583221 6675137748770431875148427)
                ·
                  refine ⟨10012706623155647812722641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675137748770431875148427 10012706623155647812722641)
                  ·
                    refine ⟨7509529967366735859541981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10012706623155647812722641 7509529967366735859541981)
                    ·
                      refine ⟨2816073737762525947328243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7509529967366735859541981 2816073737762525947328243)
                      ·
                        rfl

theorem cell23_5484284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_5484284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484284 prefixEnd_5484284 := by exact prefixLift 5484284
  have htrace : WordTrace (prefixWord ++ tailWord_5484284) baseStart_5484284 baseEnd_5484284 := by
    simpa [prefixWord, tailWord_5484284, baseEnd_5484284] using wordTrace_append hprefix tailTrace_5484284
  have hstable : (prefixWord ++ tailWord_5484284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484284).length < 2 ^ (prefixWord ++ tailWord_5484284).sum := by decide
  have hdescent : baseEnd_5484284 < baseStart_5484284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484298 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_5484298 : Nat := 118140960795 + 5484298 * 2 ^ 59
def prefixEnd_5484298 : Nat := 4983230072969 + 3 ^ 40 * 5484298 * 2
def baseEnd_5484298 : Nat := 2816080926491688892553179

theorem tailTrace_5484298 : CollatzResearch.WordTrace tailWord_5484298 prefixEnd_5484298 2816080926491688892553179 := by
  unfold tailWord_5484298
  simp only [CollatzResearch.WordTrace]
  refine ⟨50007195271333116093377387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133352520723554976249006365 50007195271333116093377387)
  ·
    refine ⟨75010792906999674140066081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50007195271333116093377387 75010792906999674140066081)
    ·
      refine ⟨56258094680249755605049561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75010792906999674140066081 56258094680249755605049561)
      ·
        refine ⟨42193571010187316703787171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56258094680249755605049561 42193571010187316703787171)
        ·
          refine ⟨63290356515280975055680757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42193571010187316703787171 63290356515280975055680757)
          ·
            refine ⟨5933470923307591411470071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63290356515280975055680757 5933470923307591411470071)
            ·
              refine ⟨8900206384961387117205107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933470923307591411470071 8900206384961387117205107)
              ·
                refine ⟨13350309577442080675807661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8900206384961387117205107 13350309577442080675807661)
                ·
                  refine ⟨5006366091540780253427873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13350309577442080675807661 5006366091540780253427873)
                  ·
                    refine ⟨3754774568655585190070905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5006366091540780253427873 3754774568655585190070905)
                    ·
                      refine ⟨2816080926491688892553179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754774568655585190070905 2816080926491688892553179)
                      ·
                        rfl

theorem cell23_5484298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_5484298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484298 prefixEnd_5484298 := by exact prefixLift 5484298
  have htrace : WordTrace (prefixWord ++ tailWord_5484298) baseStart_5484298 baseEnd_5484298 := by
    simpa [prefixWord, tailWord_5484298, baseEnd_5484298] using wordTrace_append hprefix tailTrace_5484298
  have hstable : (prefixWord ++ tailWord_5484298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484298).length < 2 ^ (prefixWord ++ tailWord_5484298).sum := by decide
  have hdescent : baseEnd_5484298 < baseStart_5484298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484357 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_5484357 : Nat := 118140960795 + 5484357 * 2 ^ 59
def prefixEnd_5484357 : Nat := 4983230072969 + 3 ^ 40 * 5484357 * 2
def baseEnd_5484357 : Nat := 2816111221850304161715407

theorem tailTrace_5484357 : CollatzResearch.WordTrace tailWord_5484357 prefixEnd_5484357 2816111221850304161715407 := by
  unfold tailWord_5484357
  simp only [CollatzResearch.WordTrace]
  refine ⟨200030932992118717449907325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133353955328079144966604883 200030932992118717449907325)
  ·
    refine ⟨75011599872044519043715247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200030932992118717449907325 75011599872044519043715247)
    ·
      refine ⟨112517399808066778565572871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75011599872044519043715247 112517399808066778565572871)
      ·
        refine ⟨168776099712100167848359307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112517399808066778565572871 168776099712100167848359307)
        ·
          refine ⟨253164149568150251772538961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168776099712100167848359307 253164149568150251772538961)
          ·
            refine ⟨189873112176112688829404221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253164149568150251772538961 189873112176112688829404221)
            ·
              refine ⟨71202417066042258311026583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189873112176112688829404221 71202417066042258311026583)
              ·
                refine ⟨106803625599063387466539875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71202417066042258311026583 106803625599063387466539875)
                ·
                  refine ⟨160205438398595081199809813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106803625599063387466539875 160205438398595081199809813)
                  ·
                    refine ⟨7509629924934144431241085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 160205438398595081199809813 7509629924934144431241085)
                    ·
                      refine ⟨2816111221850304161715407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7509629924934144431241085 2816111221850304161715407)
                      ·
                        rfl

theorem cell23_5484357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_5484357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484357 prefixEnd_5484357 := by exact prefixLift 5484357
  have htrace : WordTrace (prefixWord ++ tailWord_5484357) baseStart_5484357 baseEnd_5484357 := by
    simpa [prefixWord, tailWord_5484357, baseEnd_5484357] using wordTrace_append hprefix tailTrace_5484357
  have hstable : (prefixWord ++ tailWord_5484357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484357).length < 2 ^ (prefixWord ++ tailWord_5484357).sum := by decide
  have hdescent : baseEnd_5484357 < baseStart_5484357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484364 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_5484364 : Nat := 118140960795 + 5484364 * 2 ^ 59
def prefixEnd_5484364 : Nat := 4983230072969 + 3 ^ 40 * 5484364 * 2
def baseEnd_5484364 : Nat := 938704938738295211442625

theorem tailTrace_5484364 : CollatzResearch.WordTrace tailWord_5484364 prefixEnd_5484364 938704938738295211442625 := by
  unfold tailWord_5484364
  simp only [CollatzResearch.WordTrace]
  refine ⟨100015594151546678822706073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133354125535395571763608097 100015594151546678822706073)
  ·
    refine ⟨75011695613660009117029555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100015594151546678822706073 75011695613660009117029555)
    ·
      refine ⟨112517543420490013675544333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75011695613660009117029555 112517543420490013675544333)
      ·
        refine ⟨42194078782683755128329125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112517543420490013675544333 42194078782683755128329125)
        ·
          refine ⟨7911389771753204086561711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42194078782683755128329125 7911389771753204086561711)
          ·
            refine ⟨11867084657629806129842567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7911389771753204086561711 11867084657629806129842567)
            ·
              refine ⟨17800626986444709194763851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11867084657629806129842567 17800626986444709194763851)
              ·
                refine ⟨26700940479667063792145777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17800626986444709194763851 26700940479667063792145777)
                ·
                  refine ⟨20025705359750297844109333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26700940479667063792145777 20025705359750297844109333)
                  ·
                    refine ⟨938704938738295211442625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20025705359750297844109333 938704938738295211442625)
                    ·
                      rfl

theorem cell23_5484364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_5484364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484364 prefixEnd_5484364 := by exact prefixLift 5484364
  have htrace : WordTrace (prefixWord ++ tailWord_5484364) baseStart_5484364 baseEnd_5484364 := by
    simpa [prefixWord, tailWord_5484364, baseEnd_5484364] using wordTrace_append hprefix tailTrace_5484364
  have hstable : (prefixWord ++ tailWord_5484364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484364).length < 2 ^ (prefixWord ++ tailWord_5484364).sum := by decide
  have hdescent : baseEnd_5484364 < baseStart_5484364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484377 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 7]
def baseStart_5484377 : Nat := 118140960795 + 5484377 * 2 ^ 59
def prefixEnd_5484377 : Nat := 4983230072969 + 3 ^ 40 * 5484377 * 2
def baseEnd_5484377 : Nat := 312902387940377120385035

theorem tailTrace_5484377 : CollatzResearch.WordTrace tailWord_5484377 prefixEnd_5484377 312902387940377120385035 := by
  unfold tailWord_5484377
  simp only [CollatzResearch.WordTrace]
  refine ⟨200031662452046260865635385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133354441634697507243756923 200031662452046260865635385)
  ·
    refine ⟨150023746839034695649226539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200031662452046260865635385 150023746839034695649226539)
    ·
      refine ⟨225035620258552043473839809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150023746839034695649226539 225035620258552043473839809)
      ·
        refine ⟨168776715193914032605379857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225035620258552043473839809 168776715193914032605379857)
        ·
          refine ⟨126582536395435524454034893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168776715193914032605379857 126582536395435524454034893)
          ·
            refine ⟨47468451148288321670263085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126582536395435524454034893 47468451148288321670263085)
            ·
              refine ⟨17800669180608120626348657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47468451148288321670263085 17800669180608120626348657)
              ·
                refine ⟨13350501885456090469761493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17800669180608120626348657 13350501885456090469761493)
                ·
                  refine ⟨312902387940377120385035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13350501885456090469761493 312902387940377120385035)
                  ·
                    rfl

theorem cell23_5484377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_5484377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484377 prefixEnd_5484377 := by exact prefixLift 5484377
  have htrace : WordTrace (prefixWord ++ tailWord_5484377) baseStart_5484377 baseEnd_5484377 := by
    simpa [prefixWord, tailWord_5484377, baseEnd_5484377] using wordTrace_append hprefix tailTrace_5484377
  have hstable : (prefixWord ++ tailWord_5484377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484377).length < 2 ^ (prefixWord ++ tailWord_5484377).sum := by decide
  have hdescent : baseEnd_5484377 < baseStart_5484377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484437 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_5484437 : Nat := 118140960795 + 5484437 * 2 ^ 59
def prefixEnd_5484437 : Nat := 4983230072969 + 3 ^ 40 * 5484437 * 2
def baseEnd_5484437 : Nat := 938717433434221282905013

theorem tailTrace_5484437 : CollatzResearch.WordTrace tailWord_5484437 prefixEnd_5484437 938717433434221282905013 := by
  unfold tailWord_5484437
  simp only [CollatzResearch.WordTrace]
  refine ⟨200033850831828891112819565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133355900554552594075213043 200033850831828891112819565)
  ·
    refine ⟨75012694061935834167307337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200033850831828891112819565 75012694061935834167307337)
    ·
      refine ⟨56259520546451875625480503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75012694061935834167307337 56259520546451875625480503)
      ·
        refine ⟨84389280819677813438220755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56259520546451875625480503 84389280819677813438220755)
        ·
          refine ⟨126583921229516720157331133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84389280819677813438220755 126583921229516720157331133)
          ·
            refine ⟨47468970461068770058999175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126583921229516720157331133 47468970461068770058999175)
            ·
              refine ⟨71203455691603155088498763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47468970461068770058999175 71203455691603155088498763)
              ·
                refine ⟨106805183537404732632748145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71203455691603155088498763 106805183537404732632748145)
                ·
                  refine ⟨80103887653053549474561109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106805183537404732632748145 80103887653053549474561109)
                  ·
                    refine ⟨938717433434221282905013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80103887653053549474561109 938717433434221282905013)
                    ·
                      rfl

theorem cell23_5484437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_5484437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484437 prefixEnd_5484437 := by exact prefixLift 5484437
  have htrace : WordTrace (prefixWord ++ tailWord_5484437) baseStart_5484437 baseEnd_5484437 := by
    simpa [prefixWord, tailWord_5484437, baseEnd_5484437] using wordTrace_append hprefix tailTrace_5484437
  have hstable : (prefixWord ++ tailWord_5484437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484437).length < 2 ^ (prefixWord ++ tailWord_5484437).sum := by decide
  have hdescent : baseEnd_5484437 < baseStart_5484437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484457 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_5484457 : Nat := 118140960795 + 5484457 * 2 ^ 59
def prefixEnd_5484457 : Nat := 4983230072969 + 3 ^ 40 * 5484457 * 2
def baseEnd_5484457 : Nat := 2816162569915753770464947

theorem tailTrace_5484457 : CollatzResearch.WordTrace tailWord_5484457 prefixEnd_5484457 2816162569915753770464947 := by
  unfold tailWord_5484457
  simp only [CollatzResearch.WordTrace]
  refine ⟨200034580291756434528547625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133356386861170956352365083 200034580291756434528547625)
  ·
    refine ⟨150025935218817325896410719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200034580291756434528547625 150025935218817325896410719)
    ·
      refine ⟨225038902828225988844616079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150025935218817325896410719 225038902828225988844616079)
      ·
        refine ⟨337558354242338983266924119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225038902828225988844616079 337558354242338983266924119)
        ·
          refine ⟨506337531363508474900386179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337558354242338983266924119 506337531363508474900386179)
          ·
            refine ⟨759506297045262712350579269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506337531363508474900386179 759506297045262712350579269)
            ·
              refine ⟨142407430695986758565733613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 759506297045262712350579269 142407430695986758565733613)
              ·
                refine ⟨53402786510995034462150105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142407430695986758565733613 53402786510995034462150105)
                ·
                  refine ⟨40052089883246275846612579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53402786510995034462150105 40052089883246275846612579)
                  ·
                    refine ⟨60078134824869413769918869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40052089883246275846612579 60078134824869413769918869)
                    ·
                      refine ⟨2816162569915753770464947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60078134824869413769918869 2816162569915753770464947)
                      ·
                        rfl

theorem cell23_5484457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_5484457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484457 prefixEnd_5484457 := by exact prefixLift 5484457
  have htrace : WordTrace (prefixWord ++ tailWord_5484457) baseStart_5484457 baseEnd_5484457 := by
    simpa [prefixWord, tailWord_5484457, baseEnd_5484457] using wordTrace_append hprefix tailTrace_5484457
  have hstable : (prefixWord ++ tailWord_5484457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484457).length < 2 ^ (prefixWord ++ tailWord_5484457).sum := by decide
  have hdescent : baseEnd_5484457 < baseStart_5484457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484462 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_5484462 : Nat := 118140960795 + 5484462 * 2 ^ 59
def prefixEnd_5484462 : Nat := 4983230072969 + 3 ^ 40 * 5484462 * 2
def baseEnd_5484462 : Nat := 312907237479891805655825

theorem tailTrace_5484462 : CollatzResearch.WordTrace tailWord_5484462 prefixEnd_5484462 312907237479891805655825 := by
  unfold tailWord_5484462
  simp only [CollatzResearch.WordTrace]
  refine ⟨25004345332092290047809955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133356508437825546921653093 25004345332092290047809955)
  ·
    refine ⟨37506517998138435071714933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25004345332092290047809955 37506517998138435071714933)
    ·
      refine ⟨3516236062325478287973275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37506517998138435071714933 3516236062325478287973275)
      ·
        refine ⟨5274354093488217431959913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3516236062325478287973275 5274354093488217431959913)
        ·
          refine ⟨3955765570116163073969935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5274354093488217431959913 3955765570116163073969935)
          ·
            refine ⟨5933648355174244610954903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955765570116163073969935 5933648355174244610954903)
            ·
              refine ⟨8900472532761366916432355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5933648355174244610954903 8900472532761366916432355)
              ·
                refine ⟨13350708799142050374648533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8900472532761366916432355 13350708799142050374648533)
                ·
                  refine ⟨312907237479891805655825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13350708799142050374648533 312907237479891805655825)
                  ·
                    rfl

theorem cell23_5484462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_5484462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484462 prefixEnd_5484462 := by exact prefixLift 5484462
  have htrace : WordTrace (prefixWord ++ tailWord_5484462) baseStart_5484462 baseEnd_5484462 := by
    simpa [prefixWord, tailWord_5484462, baseEnd_5484462] using wordTrace_append hprefix tailTrace_5484462
  have hstable : (prefixWord ++ tailWord_5484462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484462).length < 2 ^ (prefixWord ++ tailWord_5484462).sum := by decide
  have hdescent : baseEnd_5484462 < baseStart_5484462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484467 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 8]
def baseStart_5484467 : Nat := 118140960795 + 5484467 * 2 ^ 59
def prefixEnd_5484467 : Nat := 4983230072969 + 3 ^ 40 * 5484467 * 2
def baseEnd_5484467 : Nat := 312907522746922081259989

theorem tailTrace_5484467 : CollatzResearch.WordTrace tailWord_5484467 prefixEnd_5484467 312907522746922081259989 := by
  unfold tailWord_5484467
  simp only [CollatzResearch.WordTrace]
  refine ⟨200034945021720206236411655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133356630014480137490941103 200034945021720206236411655)
  ·
    refine ⟨300052417532580309354617483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200034945021720206236411655 300052417532580309354617483)
    ·
      refine ⟨450078626298870464031926225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300052417532580309354617483 450078626298870464031926225)
      ·
        refine ⟨337558969724152848023944669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450078626298870464031926225 337558969724152848023944669)
        ·
          refine ⟨126584613646557318008979251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337558969724152848023944669 126584613646557318008979251)
          ·
            refine ⟨189876920469835977013468877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126584613646557318008979251 189876920469835977013468877)
            ·
              refine ⟨71203845176188491380050829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189876920469835977013468877 71203845176188491380050829)
              ·
                refine ⟨26701441941070684267519061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71203845176188491380050829 26701441941070684267519061)
                ·
                  refine ⟨312907522746922081259989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26701441941070684267519061 312907522746922081259989)
                  ·
                    rfl

theorem cell23_5484467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 8].length) (baseStart_5484467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484467 prefixEnd_5484467 := by exact prefixLift 5484467
  have htrace : WordTrace (prefixWord ++ tailWord_5484467) baseStart_5484467 baseEnd_5484467 := by
    simpa [prefixWord, tailWord_5484467, baseEnd_5484467] using wordTrace_append hprefix tailTrace_5484467
  have hstable : (prefixWord ++ tailWord_5484467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484467).length < 2 ^ (prefixWord ++ tailWord_5484467).sum := by decide
  have hdescent : baseEnd_5484467 < baseStart_5484467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484468 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_5484468 : Nat := 118140960795 + 5484468 * 2 ^ 59
def prefixEnd_5484468 : Nat := 4983230072969 + 3 ^ 40 * 5484468 * 2
def baseEnd_5484468 : Nat := 2816168218202953227427397

theorem tailTrace_5484468 : CollatzResearch.WordTrace tailWord_5484468 prefixEnd_5484468 2816168218202953227427397 := by
  unfold tailWord_5484468
  simp only [CollatzResearch.WordTrace]
  refine ⟨100017490747358291703599029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133356654329811055604798705 100017490747358291703599029)
  ·
    refine ⟨9376639757564839847212409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100017490747358291703599029 9376639757564839847212409)
    ·
      refine ⟨7032479818173629885409307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9376639757564839847212409 7032479818173629885409307)
      ·
        refine ⟨10548719727260444828113961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7032479818173629885409307 10548719727260444828113961)
        ·
          refine ⟨7911539795445333621085471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10548719727260444828113961 7911539795445333621085471)
          ·
            refine ⟨11867309693168000431628207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7911539795445333621085471 11867309693168000431628207)
            ·
              refine ⟨17800964539752000647442311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11867309693168000431628207 17800964539752000647442311)
              ·
                refine ⟨26701446809628000971163467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17800964539752000647442311 26701446809628000971163467)
                ·
                  refine ⟨40052170214442001456745201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26701446809628000971163467 40052170214442001456745201)
                  ·
                    refine ⟨30039127660831501092558901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40052170214442001456745201 30039127660831501092558901)
                    ·
                      refine ⟨2816168218202953227427397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30039127660831501092558901 2816168218202953227427397)
                      ·
                        rfl

theorem cell23_5484468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_5484468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484468 prefixEnd_5484468 := by exact prefixLift 5484468
  have htrace : WordTrace (prefixWord ++ tailWord_5484468) baseStart_5484468 baseEnd_5484468 := by
    simpa [prefixWord, tailWord_5484468, baseEnd_5484468] using wordTrace_append hprefix tailTrace_5484468
  have hstable : (prefixWord ++ tailWord_5484468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484468).length < 2 ^ (prefixWord ++ tailWord_5484468).sum := by decide
  have hdescent : baseEnd_5484468 < baseStart_5484468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484551 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5484551 : Nat := 118140960795 + 5484551 * 2 ^ 59
def prefixEnd_5484551 : Nat := 4983230072969 + 3 ^ 40 * 5484551 * 2
def baseEnd_5484551 : Nat := 2816210837097276402689515

theorem tailTrace_5484551 : CollatzResearch.WordTrace tailWord_5484551 prefixEnd_5484551 2816210837097276402689515 := by
  unfold tailWord_5484551
  simp only [CollatzResearch.WordTrace]
  refine ⟨200038008753415888582469507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133358672502277259054979671 200038008753415888582469507)
  ·
    refine ⟨300057013130123832873704261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200038008753415888582469507 300057013130123832873704261)
    ·
      refine ⟨56260689961898218663819549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300057013130123832873704261 56260689961898218663819549)
      ·
        refine ⟨21097758735711831998932331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56260689961898218663819549 21097758735711831998932331)
        ·
          refine ⟨31646638103567747998398497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21097758735711831998932331 31646638103567747998398497)
          ·
            refine ⟨23734978577675810998798873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31646638103567747998398497 23734978577675810998798873)
            ·
              refine ⟨17801233933256858249099155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23734978577675810998798873 17801233933256858249099155)
              ·
                refine ⟨26701850899885287373648733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17801233933256858249099155 26701850899885287373648733)
                ·
                  refine ⟨10013194087456982765118275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26701850899885287373648733 10013194087456982765118275)
                  ·
                    refine ⟨15019791131185474147677413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10013194087456982765118275 15019791131185474147677413)
                    ·
                      refine ⟨2816210837097276402689515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15019791131185474147677413 2816210837097276402689515)
                      ·
                        rfl

theorem cell23_5484551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5484551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484551 prefixEnd_5484551 := by exact prefixLift 5484551
  have htrace : WordTrace (prefixWord ++ tailWord_5484551) baseStart_5484551 baseEnd_5484551 := by
    simpa [prefixWord, tailWord_5484551, baseEnd_5484551] using wordTrace_append hprefix tailTrace_5484551
  have hstable : (prefixWord ++ tailWord_5484551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484551).length < 2 ^ (prefixWord ++ tailWord_5484551).sum := by decide
  have hdescent : baseEnd_5484551 < baseStart_5484551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484565 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_5484565 : Nat := 118140960795 + 5484565 * 2 ^ 59
def prefixEnd_5484565 : Nat := 4983230072969 + 3 ^ 40 * 5484565 * 2
def baseEnd_5484565 : Nat := 938739341942146449304817

theorem tailTrace_5484565 : CollatzResearch.WordTrace tailWord_5484565 prefixEnd_5484565 938739341942146449304817 := by
  unfold tailWord_5484565
  simp only [CollatzResearch.WordTrace]
  refine ⟨200038519375365168973479149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133359012916910112648986099 200038519375365168973479149)
  ·
    refine ⟨75014444765761938365054681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200038519375365168973479149 75014444765761938365054681)
    ·
      refine ⟨56260833574321453773791011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75014444765761938365054681 56260833574321453773791011)
      ·
        refine ⟨84391250361482180660686517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56260833574321453773791011 84391250361482180660686517)
        ·
          refine ⟨7911679721388954436939361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84391250361482180660686517 7911679721388954436939361)
          ·
            refine ⟨5933759791041715827704521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7911679721388954436939361 5933759791041715827704521)
            ·
              refine ⟨4450319843281286870778391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5933759791041715827704521 4450319843281286870778391)
              ·
                refine ⟨6675479764921930306167587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450319843281286870778391 6675479764921930306167587)
                ·
                  refine ⟨10013219647382895459251381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675479764921930306167587 10013219647382895459251381)
                  ·
                    refine ⟨938739341942146449304817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10013219647382895459251381 938739341942146449304817)
                    ·
                      rfl

theorem cell23_5484565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_5484565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484565 prefixEnd_5484565 := by exact prefixLift 5484565
  have htrace : WordTrace (prefixWord ++ tailWord_5484565) baseStart_5484565 baseEnd_5484565 := by
    simpa [prefixWord, tailWord_5484565, baseEnd_5484565] using wordTrace_append hprefix tailTrace_5484565
  have hstable : (prefixWord ++ tailWord_5484565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484565).length < 2 ^ (prefixWord ++ tailWord_5484565).sum := by decide
  have hdescent : baseEnd_5484565 < baseStart_5484565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484568 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 5, 2, 2]
def baseStart_5484568 : Nat := 118140960795 + 5484568 * 2 ^ 59
def prefixEnd_5484568 : Nat := 4983230072969 + 3 ^ 40 * 5484568 * 2
def baseEnd_5484568 : Nat := 2816219566268402836176937

theorem tailTrace_5484568 : CollatzResearch.WordTrace tailWord_5484568 prefixEnd_5484568 2816219566268402836176937 := by
  unfold tailWord_5484568
  simp only [CollatzResearch.WordTrace]
  refine ⟨100019314397177150242919179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133359085862902866990558905 100019314397177150242919179)
  ·
    refine ⟨150028971595765725364378769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100019314397177150242919179 150028971595765725364378769)
    ·
      refine ⟨112521728696824294023284077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150028971595765725364378769 112521728696824294023284077)
      ·
        refine ⟨42195648261309110258731529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112521728696824294023284077 42195648261309110258731529)
        ·
          refine ⟨31646736195981832694048647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42195648261309110258731529 31646736195981832694048647)
          ·
            refine ⟨47470104293972749041072971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31646736195981832694048647 47470104293972749041072971)
            ·
              refine ⟨71205156440959123561609457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47470104293972749041072971 71205156440959123561609457)
              ·
                refine ⟨53403867330719342671207093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71205156440959123561609457 53403867330719342671207093)
                ·
                  refine ⟨5006612562254938375425665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53403867330719342671207093 5006612562254938375425665)
                  ·
                    refine ⟨3754959421691203781569249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5006612562254938375425665 3754959421691203781569249)
                    ·
                      refine ⟨2816219566268402836176937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3754959421691203781569249 2816219566268402836176937)
                      ·
                        rfl

theorem cell23_5484568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_5484568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484568 prefixEnd_5484568 := by exact prefixLift 5484568
  have htrace : WordTrace (prefixWord ++ tailWord_5484568) baseStart_5484568 baseEnd_5484568 := by
    simpa [prefixWord, tailWord_5484568, baseEnd_5484568] using wordTrace_append hprefix tailTrace_5484568
  have hstable : (prefixWord ++ tailWord_5484568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484568).length < 2 ^ (prefixWord ++ tailWord_5484568).sum := by decide
  have hdescent : baseEnd_5484568 < baseStart_5484568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484624 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_5484624 : Nat := 118140960795 + 5484624 * 2 ^ 59
def prefixEnd_5484624 : Nat := 4983230072969 + 3 ^ 40 * 5484624 * 2
def baseEnd_5484624 : Nat := 2816248321185054617076679

theorem tailTrace_5484624 : CollatzResearch.WordTrace tailWord_5484624 prefixEnd_5484624 2816248321185054617076679 := by
  unfold tailWord_5484624
  simp only [CollatzResearch.WordTrace]
  refine ⟨100020335641075711024938463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133360447521434281366584617 100020335641075711024938463)
  ·
    refine ⟨150030503461613566537407695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100020335641075711024938463 150030503461613566537407695)
    ·
      refine ⟨225045755192420349806111543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150030503461613566537407695 225045755192420349806111543)
      ·
        refine ⟨337568632788630524709167315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225045755192420349806111543 337568632788630524709167315)
        ·
          refine ⟨506352949182945787063750973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337568632788630524709167315 506352949182945787063750973)
          ·
            refine ⟨189882355943604670148906615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506352949182945787063750973 189882355943604670148906615)
            ·
              refine ⟨284823533915407005223359923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189882355943604670148906615 284823533915407005223359923)
              ·
                refine ⟨427235300873110507835039885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284823533915407005223359923 427235300873110507835039885)
                ·
                  refine ⟨160213237827416440438139957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427235300873110507835039885 160213237827416440438139957)
                  ·
                    refine ⟨15019991046320291291075621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160213237827416440438139957 15019991046320291291075621)
                    ·
                      refine ⟨2816248321185054617076679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15019991046320291291075621 2816248321185054617076679)
                      ·
                        rfl

theorem cell23_5484624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_5484624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484624 prefixEnd_5484624 := by exact prefixLift 5484624
  have htrace : WordTrace (prefixWord ++ tailWord_5484624) baseStart_5484624 baseEnd_5484624 := by
    simpa [prefixWord, tailWord_5484624, baseEnd_5484624] using wordTrace_append hprefix tailTrace_5484624
  have hstable : (prefixWord ++ tailWord_5484624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484624).length < 2 ^ (prefixWord ++ tailWord_5484624).sum := by decide
  have hdescent : baseEnd_5484624 < baseStart_5484624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484628 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_5484628 : Nat := 118140960795 + 5484628 * 2 ^ 59
def prefixEnd_5484628 : Nat := 4983230072969 + 3 ^ 40 * 5484628 * 2
def baseEnd_5484628 : Nat := 2816250375107672601426661

theorem tailTrace_5484628 : CollatzResearch.WordTrace tailWord_5484628 prefixEnd_5484628 2816250375107672601426661 := by
  unfold tailWord_5484628
  simp only [CollatzResearch.WordTrace]
  refine ⟨100020408587068465366511269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133360544782757953822015025 100020408587068465366511269)
  ·
    refine ⟨18753826610075337256220863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100020408587068465366511269 18753826610075337256220863)
    ·
      refine ⟨28130739915113005884331295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18753826610075337256220863 28130739915113005884331295)
      ·
        refine ⟨42196109872669508826496943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28130739915113005884331295 42196109872669508826496943)
        ·
          refine ⟨63294164809004263239745415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42196109872669508826496943 63294164809004263239745415)
          ·
            refine ⟨94941247213506394859618123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63294164809004263239745415 94941247213506394859618123)
            ·
              refine ⟨142411870820259592289427185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94941247213506394859618123 142411870820259592289427185)
              ·
                refine ⟨106808903115194694217070389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142411870820259592289427185 106808903115194694217070389)
                ·
                  refine ⟨10013334667049502582850349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106808903115194694217070389 10013334667049502582850349)
                  ·
                    refine ⟨3755000500143563468568881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10013334667049502582850349 3755000500143563468568881)
                    ·
                      refine ⟨2816250375107672601426661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755000500143563468568881 2816250375107672601426661)
                      ·
                        rfl

theorem cell23_5484628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_5484628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484628 prefixEnd_5484628 := by exact prefixLift 5484628
  have htrace : WordTrace (prefixWord ++ tailWord_5484628) baseStart_5484628 baseEnd_5484628 := by
    simpa [prefixWord, tailWord_5484628, baseEnd_5484628] using wordTrace_append hprefix tailTrace_5484628
  have hstable : (prefixWord ++ tailWord_5484628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484628).length < 2 ^ (prefixWord ++ tailWord_5484628).sum := by decide
  have hdescent : baseEnd_5484628 < baseStart_5484628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484652 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 3]
def baseStart_5484652 : Nat := 118140960795 + 5484652 * 2 ^ 59
def prefixEnd_5484652 : Nat := 4983230072969 + 3 ^ 40 * 5484652 * 2
def baseEnd_5484652 : Nat := 2816262698643380507526551

theorem tailTrace_5484652 : CollatzResearch.WordTrace tailWord_5484652 prefixEnd_5484652 2816262698643380507526551 := by
  unfold tailWord_5484652
  simp only [CollatzResearch.WordTrace]
  refine ⟨100020846263024991415948105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133361128350699988554597473 100020846263024991415948105)
  ·
    refine ⟨75015634697268743561961079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100020846263024991415948105 75015634697268743561961079)
    ·
      refine ⟨112523452045903115342941619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75015634697268743561961079 112523452045903115342941619)
      ·
        refine ⟨168785178068854673014412429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112523452045903115342941619 168785178068854673014412429)
        ·
          refine ⟨63294441775820502380404661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168785178068854673014412429 63294441775820502380404661)
          ·
            refine ⟨5933853916483172098162937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63294441775820502380404661 5933853916483172098162937)
            ·
              refine ⟨4450390437362379073622203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5933853916483172098162937 4450390437362379073622203)
              ·
                refine ⟨6675585656043568610433305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450390437362379073622203 6675585656043568610433305)
                ·
                  refine ⟨5006689242032676457824979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6675585656043568610433305 5006689242032676457824979)
                  ·
                    refine ⟨7510033863049014686737469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5006689242032676457824979 7510033863049014686737469)
                    ·
                      refine ⟨2816262698643380507526551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7510033863049014686737469 2816262698643380507526551)
                      ·
                        rfl

theorem cell23_5484652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 3].length) (baseStart_5484652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484652 prefixEnd_5484652 := by exact prefixLift 5484652
  have htrace : WordTrace (prefixWord ++ tailWord_5484652) baseStart_5484652 baseEnd_5484652 := by
    simpa [prefixWord, tailWord_5484652, baseEnd_5484652] using wordTrace_append hprefix tailTrace_5484652
  have hstable : (prefixWord ++ tailWord_5484652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484652).length < 2 ^ (prefixWord ++ tailWord_5484652).sum := by decide
  have hdescent : baseEnd_5484652 < baseStart_5484652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484662 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5484662 : Nat := 118140960795 + 5484662 * 2 ^ 59
def prefixEnd_5484662 : Nat := 4983230072969 + 3 ^ 40 * 5484662 * 2
def baseEnd_5484662 : Nat := 2816267833449925468401505

theorem tailTrace_5484662 : CollatzResearch.WordTrace tailWord_5484662 prefixEnd_5484662 2816267833449925468401505 := by
  unfold tailWord_5484662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12502628578500859658735015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133361371504009169693173493 12502628578500859658735015)
  ·
    refine ⟨18753942867751289488102523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12502628578500859658735015 18753942867751289488102523)
    ·
      refine ⟨28130914301626934232153785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18753942867751289488102523 28130914301626934232153785)
      ·
        refine ⟨21098185726220200674115339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28130914301626934232153785 21098185726220200674115339)
        ·
          refine ⟨31647278589330301011173009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21098185726220200674115339 31647278589330301011173009)
          ·
            refine ⟨23735458941997725758379757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31647278589330301011173009 23735458941997725758379757)
            ·
              refine ⟨8900797103249147159392409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23735458941997725758379757 8900797103249147159392409)
              ·
                refine ⟨6675597827436860369544307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8900797103249147159392409 6675597827436860369544307)
                ·
                  refine ⟨10013396741155290554316461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675597827436860369544307 10013396741155290554316461)
                  ·
                    refine ⟨3755023777933233957868673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10013396741155290554316461 3755023777933233957868673)
                    ·
                      refine ⟨2816267833449925468401505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755023777933233957868673 2816267833449925468401505)
                      ·
                        rfl

theorem cell23_5484662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5484662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484662 prefixEnd_5484662 := by exact prefixLift 5484662
  have htrace : WordTrace (prefixWord ++ tailWord_5484662) baseStart_5484662 baseEnd_5484662 := by
    simpa [prefixWord, tailWord_5484662, baseEnd_5484662] using wordTrace_append hprefix tailTrace_5484662
  have hstable : (prefixWord ++ tailWord_5484662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484662).length < 2 ^ (prefixWord ++ tailWord_5484662).sum := by decide
  have hdescent : baseEnd_5484662 < baseStart_5484662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484664 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 9]
def baseStart_5484664 : Nat := 118140960795 + 5484664 * 2 ^ 59
def prefixEnd_5484664 : Nat := 4983230072969 + 3 ^ 40 * 5484664 * 2
def baseEnd_5484664 : Nat := 312918762267914940064055

theorem tailTrace_5484664 : CollatzResearch.WordTrace tailWord_5484664 prefixEnd_5484664 312918762267914940064055 := by
  unfold tailWord_5484664
  simp only [CollatzResearch.WordTrace]
  refine ⟨100021065101003254440666523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133361420134671005920888697 100021065101003254440666523)
  ·
    refine ⟨150031597651504881660999785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100021065101003254440666523 150031597651504881660999785)
    ·
      refine ⟨112523698238628661245749839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150031597651504881660999785 112523698238628661245749839)
      ·
        refine ⟨168785547357942991868624759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112523698238628661245749839 168785547357942991868624759)
        ·
          refine ⟨253178321036914487802937139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168785547357942991868624759 253178321036914487802937139)
          ·
            refine ⟨379767481555371731704405709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253178321036914487802937139 379767481555371731704405709)
            ·
              refine ⟨142412805583264399389152141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379767481555371731704405709 142412805583264399389152141)
              ·
                refine ⟨53404802093724149770932053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142412805583264399389152141 53404802093724149770932053)
                ·
                  refine ⟨312918762267914940064055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53404802093724149770932053 312918762267914940064055)
                  ·
                    rfl

theorem cell23_5484664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 9].length) (baseStart_5484664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484664 prefixEnd_5484664 := by exact prefixLift 5484664
  have htrace : WordTrace (prefixWord ++ tailWord_5484664) baseStart_5484664 baseEnd_5484664 := by
    simpa [prefixWord, tailWord_5484664, baseEnd_5484664] using wordTrace_append hprefix tailTrace_5484664
  have hstable : (prefixWord ++ tailWord_5484664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484664).length < 2 ^ (prefixWord ++ tailWord_5484664).sum := by decide
  have hdescent : baseEnd_5484664 < baseStart_5484664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484691 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 3]
def baseStart_5484691 : Nat := 118140960795 + 5484691 * 2 ^ 59
def prefixEnd_5484691 : Nat := 4983230072969 + 3 ^ 40 * 5484691 * 2
def baseEnd_5484691 : Nat := 2816282724388905854938871

theorem tailTrace_5484691 : CollatzResearch.WordTrace tailWord_5484691 prefixEnd_5484691 2816282724388905854938871 := by
  unfold tailWord_5484691
  simp only [CollatzResearch.WordTrace]
  refine ⟨200043114972908692492565927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133362076648605794995043951 200043114972908692492565927)
  ·
    refine ⟨300064672459363038738848891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200043114972908692492565927 300064672459363038738848891)
    ·
      refine ⟨450097008689044558108273337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300064672459363038738848891 450097008689044558108273337)
      ·
        refine ⟨337572756516783418581205003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450097008689044558108273337 337572756516783418581205003)
        ·
          refine ⟨506359134775175127871807505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337572756516783418581205003 506359134775175127871807505)
          ·
            refine ⟨379769351081381345903855629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506359134775175127871807505 379769351081381345903855629)
            ·
              refine ⟨142413506655518004713945861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379769351081381345903855629 142413506655518004713945861)
              ·
                refine ⟨26702532497909625883864849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142413506655518004713945861 26702532497909625883864849)
                ·
                  refine ⟨20026899373432219412898637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26702532497909625883864849 20026899373432219412898637)
                  ·
                    refine ⟨7510087265037082279836989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20026899373432219412898637 7510087265037082279836989)
                    ·
                      refine ⟨2816282724388905854938871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7510087265037082279836989 2816282724388905854938871)
                      ·
                        rfl

theorem cell23_5484691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_5484691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484691 prefixEnd_5484691 := by exact prefixLift 5484691
  have htrace : WordTrace (prefixWord ++ tailWord_5484691) baseStart_5484691 baseEnd_5484691 := by
    simpa [prefixWord, tailWord_5484691, baseEnd_5484691] using wordTrace_append hprefix tailTrace_5484691
  have hstable : (prefixWord ++ tailWord_5484691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484691).length < 2 ^ (prefixWord ++ tailWord_5484691).sum := by decide
  have hdescent : baseEnd_5484691 < baseStart_5484691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484731 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4]
def baseStart_5484731 : Nat := 118140960795 + 5484731 * 2 ^ 59
def prefixEnd_5484731 : Nat := 4983230072969 + 3 ^ 40 * 5484731 * 2
def baseEnd_5484731 : Nat := 2816303263615085698438687

theorem tailTrace_5484731 : CollatzResearch.WordTrace tailWord_5484731 prefixEnd_5484731 2816303263615085698438687 := by
  unfold tailWord_5484731
  simp only [CollatzResearch.WordTrace]
  refine ⟨200044573892763779324022047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133363049261842519549348031 200044573892763779324022047)
  ·
    refine ⟨300066860839145668986033071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200044573892763779324022047 300066860839145668986033071)
    ·
      refine ⟨450100291258718503479049607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300066860839145668986033071 450100291258718503479049607)
      ·
        refine ⟨675150436888077755218574411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450100291258718503479049607 675150436888077755218574411)
        ·
          refine ⟨1012725655332116632827861617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675150436888077755218574411 1012725655332116632827861617)
          ·
            refine ⟨759544241499087474620896213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012725655332116632827861617 759544241499087474620896213)
            ·
              refine ⟨17801818160134862686427255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 759544241499087474620896213 17801818160134862686427255)
              ·
                refine ⟨26702727240202294029640883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17801818160134862686427255 26702727240202294029640883)
                ·
                  refine ⟨40054090860303441044461325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26702727240202294029640883 40054090860303441044461325)
                  ·
                    refine ⟨15020284072613790391672997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40054090860303441044461325 15020284072613790391672997)
                    ·
                      refine ⟨2816303263615085698438687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15020284072613790391672997 2816303263615085698438687)
                      ·
                        rfl

theorem cell23_5484731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_5484731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484731 prefixEnd_5484731 := by exact prefixLift 5484731
  have htrace : WordTrace (prefixWord ++ tailWord_5484731) baseStart_5484731 baseEnd_5484731 := by
    simpa [prefixWord, tailWord_5484731, baseEnd_5484731] using wordTrace_append hprefix tailTrace_5484731
  have hstable : (prefixWord ++ tailWord_5484731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484731).length < 2 ^ (prefixWord ++ tailWord_5484731).sum := by decide
  have hdescent : baseEnd_5484731 < baseStart_5484731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484775 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 3, 4]
def baseStart_5484775 : Nat := 118140960795 + 5484775 * 2 ^ 59
def prefixEnd_5484775 : Nat := 4983230072969 + 3 ^ 40 * 5484775 * 2
def baseEnd_5484775 : Nat := 938775285587961175429495

theorem tailTrace_5484775 : CollatzResearch.WordTrace tailWord_5484775 prefixEnd_5484775 938775285587961175429495 := by
  unfold tailWord_5484775
  simp only [CollatzResearch.WordTrace]
  refine ⟨200046178704604374838623779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133364119136402916559082519 200046178704604374838623779)
  ·
    refine ⟨300069268056906562257935669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200046178704604374838623779 300069268056906562257935669)
    ·
      refine ⟨28131493880334990211681469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 300069268056906562257935669 28131493880334990211681469)
      ·
        refine ⟨10549310205125621329380551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28131493880334990211681469 10549310205125621329380551)
        ·
          refine ⟨15823965307688431994070827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10549310205125621329380551 15823965307688431994070827)
          ·
            refine ⟨23735947961532647991106241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15823965307688431994070827 23735947961532647991106241)
            ·
              refine ⟨17801960971149485993329681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23735947961532647991106241 17801960971149485993329681)
              ·
                refine ⟨13351470728362114494997261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17801960971149485993329681 13351470728362114494997261)
                ·
                  refine ⟨5006801523135792935623973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13351470728362114494997261 5006801523135792935623973)
                  ·
                    refine ⟨938775285587961175429495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5006801523135792935623973 938775285587961175429495)
                    ·
                      rfl

theorem cell23_5484775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_5484775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484775 prefixEnd_5484775 := by exact prefixLift 5484775
  have htrace : WordTrace (prefixWord ++ tailWord_5484775) baseStart_5484775 baseEnd_5484775 := by
    simpa [prefixWord, tailWord_5484775, baseEnd_5484775] using wordTrace_append hprefix tailTrace_5484775
  have hstable : (prefixWord ++ tailWord_5484775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484775).length < 2 ^ (prefixWord ++ tailWord_5484775).sum := by decide
  have hdescent : baseEnd_5484775 < baseStart_5484775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484802 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_5484802 : Nat := 118140960795 + 5484802 * 2 ^ 59
def prefixEnd_5484802 : Nat := 4983230072969 + 3 ^ 40 * 5484802 * 2
def baseEnd_5484802 : Nat := 2816339720741554920650861

theorem tailTrace_5484802 : CollatzResearch.WordTrace tailWord_5484802 prefixEnd_5484802 2816339720741554920650861 := by
  unfold tailWord_5484802
  simp only [CollatzResearch.WordTrace]
  refine ⟨50011790868876639612464165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133364775650337705633237773 50011790868876639612464165)
  ·
    refine ⟨9377210787914369927337031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50011790868876639612464165 9377210787914369927337031)
    ·
      refine ⟨14065816181871554891005547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9377210787914369927337031 14065816181871554891005547)
      ·
        refine ⟨21098724272807332336508321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14065816181871554891005547 21098724272807332336508321)
        ·
          refine ⟨15824043204605499252381241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21098724272807332336508321 15824043204605499252381241)
          ·
            refine ⟨11868032403454124439285931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15824043204605499252381241 11868032403454124439285931)
            ·
              refine ⟨17802048605181186658928897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11868032403454124439285931 17802048605181186658928897)
              ·
                refine ⟨13351536453885889994196673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17802048605181186658928897 13351536453885889994196673)
                ·
                  refine ⟨10013652340414417495647505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13351536453885889994196673 10013652340414417495647505)
                  ·
                    refine ⟨7510239255310813121735629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10013652340414417495647505 7510239255310813121735629)
                    ·
                      refine ⟨2816339720741554920650861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7510239255310813121735629 2816339720741554920650861)
                      ·
                        rfl

theorem cell23_5484802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_5484802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484802 prefixEnd_5484802 := by exact prefixLift 5484802
  have htrace : WordTrace (prefixWord ++ tailWord_5484802) baseStart_5484802 baseEnd_5484802 := by
    simpa [prefixWord, tailWord_5484802, baseEnd_5484802] using wordTrace_append hprefix tailTrace_5484802
  have hstable : (prefixWord ++ tailWord_5484802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484802).length < 2 ^ (prefixWord ++ tailWord_5484802).sum := by decide
  have hdescent : baseEnd_5484802 < baseStart_5484802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484848 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 4, 4]
def baseStart_5484848 : Nat := 118140960795 + 5484848 * 2 ^ 59
def prefixEnd_5484848 : Nat := 4983230072969 + 3 ^ 40 * 5484848 * 2
def baseEnd_5484848 : Nat := 938787780283887246891883

theorem tailTrace_5484848 : CollatzResearch.WordTrace tailWord_5484848 prefixEnd_5484848 938787780283887246891883 := by
  unfold tailWord_5484848
  simp only [CollatzResearch.WordTrace]
  refine ⟨100024420616669954153015599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133365894155559938870687465 100024420616669954153015599)
  ·
    refine ⟨150036630925004931229523399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100024420616669954153015599 150036630925004931229523399)
    ·
      refine ⟨225054946387507396844285099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150036630925004931229523399 225054946387507396844285099)
      ·
        refine ⟨337582419581261095266427649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225054946387507396844285099 337582419581261095266427649)
        ·
          refine ⟨253186814685945821449820737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337582419581261095266427649 253186814685945821449820737)
          ·
            refine ⟨189890111014459366087365553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253186814685945821449820737 189890111014459366087365553)
            ·
              refine ⟨142417583260844524565524165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189890111014459366087365553 142417583260844524565524165)
              ·
                refine ⟨26703296861408348356035781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142417583260844524565524165 26703296861408348356035781)
                ·
                  refine ⟨5006868161514065316756709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26703296861408348356035781 5006868161514065316756709)
                  ·
                    refine ⟨938787780283887246891883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5006868161514065316756709 938787780283887246891883)
                    ·
                      rfl

theorem cell23_5484848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_5484848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484848 prefixEnd_5484848 := by exact prefixLift 5484848
  have htrace : WordTrace (prefixWord ++ tailWord_5484848) baseStart_5484848 baseEnd_5484848 := by
    simpa [prefixWord, tailWord_5484848, baseEnd_5484848] using wordTrace_append hprefix tailTrace_5484848
  have hstable : (prefixWord ++ tailWord_5484848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484848).length < 2 ^ (prefixWord ++ tailWord_5484848).sum := by decide
  have hdescent : baseEnd_5484848 < baseStart_5484848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484861 : List Nat := [1, 4, 1, 17]
def baseStart_5484861 : Nat := 118140960795 + 5484861 * 2 ^ 59
def prefixEnd_5484861 : Nat := 4983230072969 + 3 ^ 40 * 5484861 * 2
def baseEnd_5484861 : Nat := 1287777785139538266947

theorem tailTrace_5484861 : CollatzResearch.WordTrace tailWord_5484861 prefixEnd_5484861 1287777785139538266947 := by
  unfold tailWord_5484861
  simp only [CollatzResearch.WordTrace]
  refine ⟨200049315382292811526254437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133366210254861874350836291 200049315382292811526254437)
  ·
    refine ⟨37509246634179902161172707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200049315382292811526254437 37509246634179902161172707)
    ·
      refine ⟨56263869951269853241759061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37509246634179902161172707 56263869951269853241759061)
      ·
        refine ⟨1287777785139538266947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 56263869951269853241759061 1287777785139538266947)
        ·
          rfl

theorem cell23_5484861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 17].length) (baseStart_5484861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484861 prefixEnd_5484861 := by exact prefixLift 5484861
  have htrace : WordTrace (prefixWord ++ tailWord_5484861) baseStart_5484861 baseEnd_5484861 := by
    simpa [prefixWord, tailWord_5484861, baseEnd_5484861] using wordTrace_append hprefix tailTrace_5484861
  have hstable : (prefixWord ++ tailWord_5484861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484861).length < 2 ^ (prefixWord ++ tailWord_5484861).sum := by decide
  have hdescent : baseEnd_5484861 < baseStart_5484861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484891 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 13]
def baseStart_5484891 : Nat := 118140960795 + 5484891 * 2 ^ 59
def prefixEnd_5484891 : Nat := 4983230072969 + 3 ^ 40 * 5484891 * 2
def baseEnd_5484891 : Nat := 938795140173268357479317

theorem tailTrace_5484891 : CollatzResearch.WordTrace tailWord_5484891 prefixEnd_5484891 938795140173268357479317 := by
  unfold tailWord_5484891
  simp only [CollatzResearch.WordTrace]
  refine ⟨200050409572184126649846527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133366939714789417766564351 200050409572184126649846527)
  ·
    refine ⟨300075614358276189974769791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200050409572184126649846527 300075614358276189974769791)
    ·
      refine ⟨450113421537414284962154687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300075614358276189974769791 450113421537414284962154687)
      ·
        refine ⟨675170132306121427443232031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450113421537414284962154687 675170132306121427443232031)
        ·
          refine ⟨1012755198459182141164848047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675170132306121427443232031 1012755198459182141164848047)
          ·
            refine ⟨1519132797688773211747272071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012755198459182141164848047 1519132797688773211747272071)
            ·
              refine ⟨2278699196533159817620908107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519132797688773211747272071 2278699196533159817620908107)
              ·
                refine ⟨3418048794799739726431362161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278699196533159817620908107 3418048794799739726431362161)
                ·
                  refine ⟨2563536596099804794823521621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418048794799739726431362161 2563536596099804794823521621)
                  ·
                    refine ⟨938795140173268357479317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 2563536596099804794823521621 938795140173268357479317)
                    ·
                      rfl

theorem cell23_5484891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_5484891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484891 prefixEnd_5484891 := by exact prefixLift 5484891
  have htrace : WordTrace (prefixWord ++ tailWord_5484891) baseStart_5484891 baseEnd_5484891 := by
    simpa [prefixWord, tailWord_5484891, baseEnd_5484891] using wordTrace_append hprefix tailTrace_5484891
  have hstable : (prefixWord ++ tailWord_5484891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484891).length < 2 ^ (prefixWord ++ tailWord_5484891).sum := by decide
  have hdescent : baseEnd_5484891 < baseStart_5484891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484905 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 3]
def baseStart_5484905 : Nat := 118140960795 + 5484905 * 2 ^ 59
def prefixEnd_5484905 : Nat := 4983230072969 + 3 ^ 40 * 5484905 * 2
def baseEnd_5484905 : Nat := 2816392609248968017662887

theorem tailTrace_5484905 : CollatzResearch.WordTrace tailWord_5484905 prefixEnd_5484905 2816392609248968017662887 := by
  unfold tailWord_5484905
  simp only [CollatzResearch.WordTrace]
  refine ⟨200050920194133407040856169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133367280129422271360570779 200050920194133407040856169)
  ·
    refine ⟨150038190145600055280642127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200050920194133407040856169 150038190145600055280642127)
    ·
      refine ⟨225057285218400082920963191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150038190145600055280642127 225057285218400082920963191)
      ·
        refine ⟨337585927827600124381444787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225057285218400082920963191 337585927827600124381444787)
        ·
          refine ⟨506378891741400186572167181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337585927827600124381444787 506378891741400186572167181)
          ·
            refine ⟨189892084403025069964562693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506378891741400186572167181 189892084403025069964562693)
            ·
              refine ⟨35604765825567200618355505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189892084403025069964562693 35604765825567200618355505)
              ·
                refine ⟨26703574369175400463766629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35604765825567200618355505 26703574369175400463766629)
                ·
                  refine ⟨5006920194220387586956243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26703574369175400463766629 5006920194220387586956243)
                  ·
                    refine ⟨7510380291330581380434365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5006920194220387586956243 7510380291330581380434365)
                    ·
                      refine ⟨2816392609248968017662887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7510380291330581380434365 2816392609248968017662887)
                      ·
                        rfl

theorem cell23_5484905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 1, 3].length) (baseStart_5484905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484905 prefixEnd_5484905 := by exact prefixLift 5484905
  have htrace : WordTrace (prefixWord ++ tailWord_5484905) baseStart_5484905 baseEnd_5484905 := by
    simpa [prefixWord, tailWord_5484905, baseEnd_5484905] using wordTrace_append hprefix tailTrace_5484905
  have hstable : (prefixWord ++ tailWord_5484905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484905).length < 2 ^ (prefixWord ++ tailWord_5484905).sum := by decide
  have hdescent : baseEnd_5484905 < baseStart_5484905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484906 : List Nat := [3, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_5484906 : Nat := 118140960795 + 5484906 * 2 ^ 59
def prefixEnd_5484906 : Nat := 4983230072969 + 3 ^ 40 * 5484906 * 2
def baseEnd_5484906 : Nat := 2816393122729622513750383

theorem tailTrace_5484906 : CollatzResearch.WordTrace tailWord_5484906 prefixEnd_5484906 2816393122729622513750383 := by
  unfold tailWord_5484906
  simp only [CollatzResearch.WordTrace]
  refine ⟨50012739166782446052910643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133367304444753189474428381 50012739166782446052910643)
  ·
    refine ⟨75019108750173669079365965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50012739166782446052910643 75019108750173669079365965)
    ·
      refine ⟨28132165781315125904762237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75019108750173669079365965 28132165781315125904762237)
      ·
        refine ⟨10549562167993172214285839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28132165781315125904762237 10549562167993172214285839)
        ·
          refine ⟨15824343251989758321428759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10549562167993172214285839 15824343251989758321428759)
          ·
            refine ⟨23736514877984637482143139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15824343251989758321428759 23736514877984637482143139)
            ·
              refine ⟨35604772316976956223214709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23736514877984637482143139 35604772316976956223214709)
              ·
                refine ⟨3337947404716589645926379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35604772316976956223214709 3337947404716589645926379)
                ·
                  refine ⟨5006921107074884468889569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337947404716589645926379 5006921107074884468889569)
                  ·
                    refine ⟨3755190830306163351667177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5006921107074884468889569 3755190830306163351667177)
                    ·
                      refine ⟨2816393122729622513750383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755190830306163351667177 2816393122729622513750383)
                      ·
                        rfl

theorem cell23_5484906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_5484906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484906 prefixEnd_5484906 := by exact prefixLift 5484906
  have htrace : WordTrace (prefixWord ++ tailWord_5484906) baseStart_5484906 baseEnd_5484906 := by
    simpa [prefixWord, tailWord_5484906, baseEnd_5484906] using wordTrace_append hprefix tailTrace_5484906
  have hstable : (prefixWord ++ tailWord_5484906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484906).length < 2 ^ (prefixWord ++ tailWord_5484906).sum := by decide
  have hdescent : baseEnd_5484906 < baseStart_5484906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484939 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 2, 1, 3]
def baseStart_5484939 : Nat := 118140960795 + 5484939 * 2 ^ 59
def prefixEnd_5484939 : Nat := 4983230072969 + 3 ^ 40 * 5484939 * 2
def baseEnd_5484939 : Nat := 2816410067591220884637731

theorem tailTrace_5484939 : CollatzResearch.WordTrace tailWord_5484939 prefixEnd_5484939 2816410067591220884637731 := by
  unfold tailWord_5484939
  simp only [CollatzResearch.WordTrace]
  refine ⟨200052160276010230847593871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133368106850673487231729247 200052160276010230847593871)
  ·
    refine ⟨300078240414015346271390807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200052160276010230847593871 300078240414015346271390807)
    ·
      refine ⟨450117360621023019407086211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300078240414015346271390807 450117360621023019407086211)
      ·
        refine ⟨675176040931534529110629317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450117360621023019407086211 675176040931534529110629317)
        ·
          refine ⟨126595507674662724208242997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 675176040931534529110629317 126595507674662724208242997)
          ·
            refine ⟨11868328844499630394522781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126595507674662724208242997 11868328844499630394522781)
            ·
              refine ⟨4450623316687361397946043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11868328844499630394522781 4450623316687361397946043)
              ·
                refine ⟨6675934975031042096919065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450623316687361397946043 6675934975031042096919065)
                ·
                  refine ⟨5006951231273281572689299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6675934975031042096919065 5006951231273281572689299)
                  ·
                    refine ⟨7510426846909922359033949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5006951231273281572689299 7510426846909922359033949)
                    ·
                      refine ⟨2816410067591220884637731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7510426846909922359033949 2816410067591220884637731)
                      ·
                        rfl

theorem cell23_5484939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 1, 3].length) (baseStart_5484939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484939 prefixEnd_5484939 := by exact prefixLift 5484939
  have htrace : WordTrace (prefixWord ++ tailWord_5484939) baseStart_5484939 baseEnd_5484939 := by
    simpa [prefixWord, tailWord_5484939, baseEnd_5484939] using wordTrace_append hprefix tailTrace_5484939
  have hstable : (prefixWord ++ tailWord_5484939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484939).length < 2 ^ (prefixWord ++ tailWord_5484939).sum := by decide
  have hdescent : baseEnd_5484939 < baseStart_5484939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484962 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_5484962 : Nat := 118140960795 + 5484962 * 2 ^ 59
def prefixEnd_5484962 : Nat := 4983230072969 + 3 ^ 40 * 5484962 * 2
def baseEnd_5484962 : Nat := 2816421877646274294650125

theorem tailTrace_5484962 : CollatzResearch.WordTrace tailWord_5484962 prefixEnd_5484962 2816421877646274294650125 := by
  unfold tailWord_5484962
  simp only [CollatzResearch.WordTrace]
  refine ⟨50013249788731726443920285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133368666103284603850454093 50013249788731726443920285)
  ·
    refine ⟨18754968670774397416470107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50013249788731726443920285 18754968670774397416470107)
    ·
      refine ⟨28132453006161596124705161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18754968670774397416470107 28132453006161596124705161)
      ·
        refine ⟨21099339754621197093528871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28132453006161596124705161 21099339754621197093528871)
        ·
          refine ⟨31649009631931795640293307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21099339754621197093528871 31649009631931795640293307)
          ·
            refine ⟨47473514447897693460439961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31649009631931795640293307 47473514447897693460439961)
            ·
              refine ⟨35605135835923270095329971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47473514447897693460439961 35605135835923270095329971)
              ·
                refine ⟨53407703753884905142994957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35605135835923270095329971 53407703753884905142994957)
                ·
                  refine ⟨20027888907706839428623109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53407703753884905142994957 20027888907706839428623109)
                  ·
                    refine ⟨3755229170195032392866833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20027888907706839428623109 3755229170195032392866833)
                    ·
                      refine ⟨2816421877646274294650125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755229170195032392866833 2816421877646274294650125)
                      ·
                        rfl

theorem cell23_5484962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_5484962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484962 prefixEnd_5484962 := by exact prefixLift 5484962
  have htrace : WordTrace (prefixWord ++ tailWord_5484962) baseStart_5484962 baseEnd_5484962 := by
    simpa [prefixWord, tailWord_5484962, baseEnd_5484962] using wordTrace_append hprefix tailTrace_5484962
  have hstable : (prefixWord ++ tailWord_5484962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484962).length < 2 ^ (prefixWord ++ tailWord_5484962).sum := by decide
  have hdescent : baseEnd_5484962 < baseStart_5484962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484978 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_5484978 : Nat := 118140960795 + 5484978 * 2 ^ 59
def prefixEnd_5484978 : Nat := 4983230072969 + 3 ^ 40 * 5484978 * 2
def baseEnd_5484978 : Nat := 2816430093336746232050051

theorem tailTrace_5484978 : CollatzResearch.WordTrace tailWord_5484978 prefixEnd_5484978 2816430093336746232050051 := by
  unfold tailWord_5484978
  simp only [CollatzResearch.WordTrace]
  refine ⟨50013395680717235127065897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133369055148579293672175725 50013395680717235127065897)
  ·
    refine ⟨37510046760537926345299423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50013395680717235127065897 37510046760537926345299423)
    ·
      refine ⟨56265070140806889517949135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37510046760537926345299423 56265070140806889517949135)
      ·
        refine ⟨84397605211210334276923703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56265070140806889517949135 84397605211210334276923703)
        ·
          refine ⟨126596407816815501415385555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84397605211210334276923703 126596407816815501415385555)
          ·
            refine ⟨189894611725223252123078333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126596407816815501415385555 189894611725223252123078333)
            ·
              refine ⟨71210479396958719546154375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189894611725223252123078333 71210479396958719546154375)
              ·
                refine ⟨106815719095438079319231563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71210479396958719546154375 106815719095438079319231563)
                ·
                  refine ⟨160223578643157118978847345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106815719095438079319231563 160223578643157118978847345)
                  ·
                    refine ⟨120167683982367839234135509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160223578643157118978847345 120167683982367839234135509)
                    ·
                      refine ⟨2816430093336746232050051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120167683982367839234135509 2816430093336746232050051)
                      ·
                        rfl

theorem cell23_5484978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_5484978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484978 prefixEnd_5484978 := by exact prefixLift 5484978
  have htrace : WordTrace (prefixWord ++ tailWord_5484978) baseStart_5484978 baseEnd_5484978 := by
    simpa [prefixWord, tailWord_5484978, baseEnd_5484978] using wordTrace_append hprefix tailTrace_5484978
  have hstable : (prefixWord ++ tailWord_5484978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484978).length < 2 ^ (prefixWord ++ tailWord_5484978).sum := by decide
  have hdescent : baseEnd_5484978 < baseStart_5484978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5484985 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 7]
def baseStart_5484985 : Nat := 118140960795 + 5484985 * 2 ^ 59
def prefixEnd_5484985 : Nat := 4983230072969 + 3 ^ 40 * 5484985 * 2
def baseEnd_5484985 : Nat := 312937076411258633851391

theorem tailTrace_5484985 : CollatzResearch.WordTrace tailWord_5484985 prefixEnd_5484985 312937076411258633851391 := by
  unfold tailWord_5484985
  simp only [CollatzResearch.WordTrace]
  refine ⟨200053838033843580703768409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133369225355895720469178939 200053838033843580703768409)
  ·
    refine ⟨150040378525382685527826307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200053838033843580703768409 150040378525382685527826307)
    ·
      refine ⟨225060567788074028291739461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150040378525382685527826307 225060567788074028291739461)
      ·
        refine ⟨42198856460263880304701149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225060567788074028291739461 42198856460263880304701149)
        ·
          refine ⟨15824571172598955114262931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42198856460263880304701149 15824571172598955114262931)
          ·
            refine ⟨23736856758898432671394397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15824571172598955114262931 23736856758898432671394397)
            ·
              refine ⟨8901321284586912251772899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23736856758898432671394397 8901321284586912251772899)
              ·
                refine ⟨13351981926880368377659349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8901321284586912251772899 13351981926880368377659349)
                ·
                  refine ⟨312937076411258633851391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13351981926880368377659349 312937076411258633851391)
                  ·
                    rfl

theorem cell23_5484985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 7].length) (baseStart_5484985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5484985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5484985 prefixEnd_5484985 := by exact prefixLift 5484985
  have htrace : WordTrace (prefixWord ++ tailWord_5484985) baseStart_5484985 baseEnd_5484985 := by
    simpa [prefixWord, tailWord_5484985, baseEnd_5484985] using wordTrace_append hprefix tailTrace_5484985
  have hstable : (prefixWord ++ tailWord_5484985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5484985).length < 2 ^ (prefixWord ++ tailWord_5484985).sum := by decide
  have hdescent : baseEnd_5484985 < baseStart_5484985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5484985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485008 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_5485008 : Nat := 118140960795 + 5485008 * 2 ^ 59
def prefixEnd_5485008 : Nat := 4983230072969 + 3 ^ 40 * 5485008 * 2
def baseEnd_5485008 : Nat := 2816445497756381114674913

theorem tailTrace_5485008 : CollatzResearch.WordTrace tailWord_5485008 prefixEnd_5485008 2816445497756381114674913 := by
  unfold tailWord_5485008
  simp only [CollatzResearch.WordTrace]
  refine ⟨100027338456380127815927839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133369784608506837087903785 100027338456380127815927839)
  ·
    refine ⟨150041007684570191723891759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100027338456380127815927839 150041007684570191723891759)
    ·
      refine ⟨225061511526855287585837639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150041007684570191723891759 225061511526855287585837639)
      ·
        refine ⟨337592267290282931378756459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225061511526855287585837639 337592267290282931378756459)
        ·
          refine ⟨506388400935424397068134689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337592267290282931378756459 506388400935424397068134689)
          ·
            refine ⟨379791300701568297801101017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506388400935424397068134689 379791300701568297801101017)
            ·
              refine ⟨284843475526176223350825763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379791300701568297801101017 284843475526176223350825763)
              ·
                refine ⟨427265213289264335026238645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284843475526176223350825763 427265213289264335026238645)
                ·
                  refine ⟨40056113745868531408709873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 427265213289264335026238645 40056113745868531408709873)
                  ·
                    refine ⟨30042085309401398556532405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40056113745868531408709873 30042085309401398556532405)
                    ·
                      refine ⟨2816445497756381114674913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30042085309401398556532405 2816445497756381114674913)
                      ·
                        rfl

theorem cell23_5485008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_5485008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485008 prefixEnd_5485008 := by exact prefixLift 5485008
  have htrace : WordTrace (prefixWord ++ tailWord_5485008) baseStart_5485008 baseEnd_5485008 := by
    simpa [prefixWord, tailWord_5485008, baseEnd_5485008] using wordTrace_append hprefix tailTrace_5485008
  have hstable : (prefixWord ++ tailWord_5485008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485008).length < 2 ^ (prefixWord ++ tailWord_5485008).sum := by decide
  have hdescent : baseEnd_5485008 < baseStart_5485008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485035 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 4]
def baseStart_5485035 : Nat := 118140960795 + 5485035 * 2 ^ 59
def prefixEnd_5485035 : Nat := 4983230072969 + 3 ^ 40 * 5485035 * 2
def baseEnd_5485035 : Nat := 2816459361734052509037289

theorem tailTrace_5485035 : CollatzResearch.WordTrace tailWord_5485035 prefixEnd_5485035 2816459361734052509037289 := by
  unfold tailWord_5485035
  simp only [CollatzResearch.WordTrace]
  refine ⟨200055661683662439243088559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133370441122441626162059039 200055661683662439243088559)
  ·
    refine ⟨300083492525493658864632839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200055661683662439243088559 300083492525493658864632839)
    ·
      refine ⟨450125238788240488296949259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300083492525493658864632839 450125238788240488296949259)
      ·
        refine ⟨675187858182360732445423889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450125238788240488296949259 675187858182360732445423889)
        ·
          refine ⟨506390893636770549334067917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675187858182360732445423889 506390893636770549334067917)
          ·
            refine ⟨189896585113788956000275469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 506390893636770549334067917 189896585113788956000275469)
            ·
              refine ⟨71211219417670858500103301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189896585113788956000275469 71211219417670858500103301)
              ·
                refine ⟨13352103640813285968769369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71211219417670858500103301 13352103640813285968769369)
                ·
                  refine ⟨10014077730609964476577027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13352103640813285968769369 10014077730609964476577027)
                  ·
                    refine ⟨15021116595914946714865541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10014077730609964476577027 15021116595914946714865541)
                    ·
                      refine ⟨2816459361734052509037289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15021116595914946714865541 2816459361734052509037289)
                      ·
                        rfl

theorem cell23_5485035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 4].length) (baseStart_5485035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485035 prefixEnd_5485035 := by exact prefixLift 5485035
  have htrace : WordTrace (prefixWord ++ tailWord_5485035) baseStart_5485035 baseEnd_5485035 := by
    simpa [prefixWord, tailWord_5485035, baseEnd_5485035] using wordTrace_append hprefix tailTrace_5485035
  have hstable : (prefixWord ++ tailWord_5485035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485035).length < 2 ^ (prefixWord ++ tailWord_5485035).sum := by decide
  have hdescent : baseEnd_5485035 < baseStart_5485035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485055 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 3]
def baseStart_5485055 : Nat := 118140960795 + 5485055 * 2 ^ 59
def prefixEnd_5485055 : Nat := 4983230072969 + 3 ^ 40 * 5485055 * 2
def baseEnd_5485055 : Nat := 2816469631347142430787197

theorem tailTrace_5485055 : CollatzResearch.WordTrace tailWord_5485055 prefixEnd_5485055 2816469631347142430787197 := by
  unfold tailWord_5485055
  simp only [CollatzResearch.WordTrace]
  refine ⟨200056391143589982658816619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133370927429059988439211079 200056391143589982658816619)
  ·
    refine ⟨300084586715384973988224929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200056391143589982658816619 300084586715384973988224929)
    ·
      refine ⟨225063440036538730491168697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300084586715384973988224929 225063440036538730491168697)
      ·
        refine ⟨168797580027404047868376523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225063440036538730491168697 168797580027404047868376523)
        ·
          refine ⟨253196370041106071802564785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168797580027404047868376523 253196370041106071802564785)
          ·
            refine ⟨189897277530829553851923589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253196370041106071802564785 189897277530829553851923589)
            ·
              refine ⟨35605739537030541347235673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189897277530829553851923589 35605739537030541347235673)
              ·
                refine ⟨26704304652772906010426755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35605739537030541347235673 26704304652772906010426755)
                ·
                  refine ⟨40056456979159359015640133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26704304652772906010426755 40056456979159359015640133)
                  ·
                    refine ⟨7510585683592379815432525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40056456979159359015640133 7510585683592379815432525)
                    ·
                      refine ⟨2816469631347142430787197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7510585683592379815432525 2816469631347142430787197)
                      ·
                        rfl

theorem cell23_5485055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_5485055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485055 prefixEnd_5485055 := by exact prefixLift 5485055
  have htrace : WordTrace (prefixWord ++ tailWord_5485055) baseStart_5485055 baseEnd_5485055 := by
    simpa [prefixWord, tailWord_5485055, baseEnd_5485055] using wordTrace_append hprefix tailTrace_5485055
  have hstable : (prefixWord ++ tailWord_5485055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485055).length < 2 ^ (prefixWord ++ tailWord_5485055).sum := by decide
  have hdescent : baseEnd_5485055 < baseStart_5485055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485096 : List Nat := [2, 1, 5, 2, 1, 1, 2, 4, 1, 4]
def baseStart_5485096 : Nat := 118140960795 + 5485096 * 2 ^ 59
def prefixEnd_5485096 : Nat := 4983230072969 + 3 ^ 40 * 5485096 * 2
def baseEnd_5485096 : Nat := 938830228017992256791503

theorem tailTrace_5485096 : CollatzResearch.WordTrace tailWord_5485096 prefixEnd_5485096 938830228017992256791503 := by
  unfold tailWord_5485096
  simp only [CollatzResearch.WordTrace]
  refine ⟨100028943268220723330529571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133371924357627631107372761 100028943268220723330529571)
  ·
    refine ⟨150043414902331084995794357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100028943268220723330529571 150043414902331084995794357)
    ·
      refine ⟨14066570147093539218355721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 150043414902331084995794357 14066570147093539218355721)
      ·
        refine ⟨10549927610320154413766791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14066570147093539218355721 10549927610320154413766791)
        ·
          refine ⟨15824891415480231620650187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10549927610320154413766791 15824891415480231620650187)
          ·
            refine ⟨23737337123220347430975281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15824891415480231620650187 23737337123220347430975281)
            ·
              refine ⟨17803002842415260573231461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23737337123220347430975281 17803002842415260573231461)
              ·
                refine ⟨3338063032952861357480899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17803002842415260573231461 3338063032952861357480899)
                ·
                  refine ⟨5007094549429292036221349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338063032952861357480899 5007094549429292036221349)
                  ·
                    refine ⟨938830228017992256791503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007094549429292036221349 938830228017992256791503)
                    ·
                      rfl

theorem cell23_5485096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_5485096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485096 prefixEnd_5485096 := by exact prefixLift 5485096
  have htrace : WordTrace (prefixWord ++ tailWord_5485096) baseStart_5485096 baseEnd_5485096 := by
    simpa [prefixWord, tailWord_5485096, baseEnd_5485096] using wordTrace_append hprefix tailTrace_5485096
  have hstable : (prefixWord ++ tailWord_5485096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485096).length < 2 ^ (prefixWord ++ tailWord_5485096).sum := by decide
  have hdescent : baseEnd_5485096 < baseStart_5485096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485105 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 5, 5]
def baseStart_5485105 : Nat := 118140960795 + 5485105 * 2 ^ 59
def prefixEnd_5485105 : Nat := 4983230072969 + 3 ^ 40 * 5485105 * 2
def baseEnd_5485105 : Nat := 938831768459955745053989

theorem tailTrace_5485105 : CollatzResearch.WordTrace tailWord_5485105 prefixEnd_5485105 938831768459955745053989 := by
  unfold tailWord_5485105
  simp only [CollatzResearch.WordTrace]
  refine ⟨200058214793408841198136769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133372143195605894132091179 200058214793408841198136769)
  ·
    refine ⟨150043661095056630898602577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200058214793408841198136769 150043661095056630898602577)
    ·
      refine ⟨112532745821292473173951933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150043661095056630898602577 112532745821292473173951933)
      ·
        refine ⟨42199779682984677440231975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112532745821292473173951933 42199779682984677440231975)
        ·
          refine ⟨63299669524477016160347963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42199779682984677440231975 63299669524477016160347963)
          ·
            refine ⟨94949504286715524240521945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63299669524477016160347963 94949504286715524240521945)
            ·
              refine ⟨71212128215036643180391459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94949504286715524240521945 71212128215036643180391459)
              ·
                refine ⟨106818192322554964770587189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71212128215036643180391459 106818192322554964770587189)
                ·
                  refine ⟨10014205530239527947242549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106818192322554964770587189 10014205530239527947242549)
                  ·
                    refine ⟨938831768459955745053989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10014205530239527947242549 938831768459955745053989)
                    ·
                      rfl

theorem cell23_5485105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_5485105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485105 prefixEnd_5485105 := by exact prefixLift 5485105
  have htrace : WordTrace (prefixWord ++ tailWord_5485105) baseStart_5485105 baseEnd_5485105 := by
    simpa [prefixWord, tailWord_5485105, baseEnd_5485105] using wordTrace_append hprefix tailTrace_5485105
  have hstable : (prefixWord ++ tailWord_5485105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485105).length < 2 ^ (prefixWord ++ tailWord_5485105).sum := by decide
  have hdescent : baseEnd_5485105 < baseStart_5485105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485112 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 3, 5, 2]
def baseStart_5485112 : Nat := 118140960795 + 5485112 * 2 ^ 59
def prefixEnd_5485112 : Nat := 4983230072969 + 3 ^ 40 * 5485112 * 2
def baseEnd_5485112 : Nat := 2816498899744448707774435

theorem tailTrace_5485112 : CollatzResearch.WordTrace tailWord_5485112 prefixEnd_5485112 2816498899744448707774435 := by
  unfold tailWord_5485112
  simp only [CollatzResearch.WordTrace]
  refine ⟨100029235052191740696820795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133372313402922320929094393 100029235052191740696820795)
  ·
    refine ⟨150043852578287611045231193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100029235052191740696820795 150043852578287611045231193)
    ·
      refine ⟨112532889433715708283923395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150043852578287611045231193 112532889433715708283923395)
      ·
        refine ⟨168799334150573562425885093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112532889433715708283923395 168799334150573562425885093)
        ·
          refine ⟨31649875153232542954853455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168799334150573562425885093 31649875153232542954853455)
          ·
            refine ⟨47474812729848814432280183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31649875153232542954853455 47474812729848814432280183)
            ·
              refine ⟨71212219094773221648420275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47474812729848814432280183 71212219094773221648420275)
              ·
                refine ⟨106818328642159832472630413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71212219094773221648420275 106818328642159832472630413)
                ·
                  refine ⟨40056873240809937177236405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106818328642159832472630413 40056873240809937177236405)
                  ·
                    refine ⟨3755331866325931610365913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40056873240809937177236405 3755331866325931610365913)
                    ·
                      refine ⟨2816498899744448707774435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755331866325931610365913 2816498899744448707774435)
                      ·
                        rfl

theorem cell23_5485112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_5485112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485112 prefixEnd_5485112 := by exact prefixLift 5485112
  have htrace : WordTrace (prefixWord ++ tailWord_5485112) baseStart_5485112 baseEnd_5485112 := by
    simpa [prefixWord, tailWord_5485112, baseEnd_5485112] using wordTrace_append hprefix tailTrace_5485112
  have hstable : (prefixWord ++ tailWord_5485112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485112).length < 2 ^ (prefixWord ++ tailWord_5485112).sum := by decide
  have hdescent : baseEnd_5485112 < baseStart_5485112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485135 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 1, 6]
def baseStart_5485135 : Nat := 118140960795 + 5485135 * 2 ^ 59
def prefixEnd_5485135 : Nat := 4983230072969 + 3 ^ 40 * 5485135 * 2
def baseEnd_5485135 : Nat := 938836903266500705928943

theorem tailTrace_5485135 : CollatzResearch.WordTrace tailWord_5485135 prefixEnd_5485135 938836903266500705928943 := by
  unfold tailWord_5485135
  simp only [CollatzResearch.WordTrace]
  refine ⟨200059308983300156321728859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133372872655533437547819239 200059308983300156321728859)
  ·
    refine ⟨300088963474950234482593289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200059308983300156321728859 300088963474950234482593289)
    ·
      refine ⟨225066722606212675861944967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300088963474950234482593289 225066722606212675861944967)
      ·
        refine ⟨337600083909319013792917451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225066722606212675861944967 337600083909319013792917451)
        ·
          refine ⟨506400125863978520689376177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337600083909319013792917451 506400125863978520689376177)
          ·
            refine ⟨379800094397983890517032133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506400125863978520689376177 379800094397983890517032133)
            ·
              refine ⟨71212517699621979471943525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 379800094397983890517032133 71212517699621979471943525)
              ·
                refine ⟨13352347068679121150989411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71212517699621979471943525 13352347068679121150989411)
                ·
                  refine ⟨20028520603018681726484117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13352347068679121150989411 20028520603018681726484117)
                  ·
                    refine ⟨938836903266500705928943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20028520603018681726484117 938836903266500705928943)
                    ·
                      rfl

theorem cell23_5485135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_5485135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485135 prefixEnd_5485135 := by exact prefixLift 5485135
  have htrace : WordTrace (prefixWord ++ tailWord_5485135) baseStart_5485135 baseEnd_5485135 := by
    simpa [prefixWord, tailWord_5485135, baseEnd_5485135] using wordTrace_append hprefix tailTrace_5485135
  have hstable : (prefixWord ++ tailWord_5485135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485135).length < 2 ^ (prefixWord ++ tailWord_5485135).sum := by decide
  have hdescent : baseEnd_5485135 < baseStart_5485135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485152 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 4, 4]
def baseStart_5485152 : Nat := 118140960795 + 5485152 * 2 ^ 59
def prefixEnd_5485152 : Nat := 4983230072969 + 3 ^ 40 * 5485152 * 2
def baseEnd_5485152 : Nat := 938839812990209517091417

theorem tailTrace_5485152 : CollatzResearch.WordTrace tailWord_5485152 prefixEnd_5485152 938839812990209517091417 := by
  unfold tailWord_5485152
  simp only [CollatzResearch.WordTrace]
  refine ⟨100029964512119284112548855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133373286016159045483398473 100029964512119284112548855)
  ·
    refine ⟨150044946768178926168823283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100029964512119284112548855 150044946768178926168823283)
    ·
      refine ⟨225067420152268389253234925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150044946768178926168823283 225067420152268389253234925)
      ·
        refine ⟨84400282557100645969963097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225067420152268389253234925 84400282557100645969963097)
        ·
          refine ⟨63300211917825484477472323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84400282557100645969963097 63300211917825484477472323)
          ·
            refine ⟨94950317876738226716208485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63300211917825484477472323 94950317876738226716208485)
            ·
              refine ⟨17803184601888417509289091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94950317876738226716208485 17803184601888417509289091)
              ·
                refine ⟨26704776902832626263933637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17803184601888417509289091 26704776902832626263933637)
                ·
                  refine ⟨5007145669281117424487557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26704776902832626263933637 5007145669281117424487557)
                  ·
                    refine ⟨938839812990209517091417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007145669281117424487557 938839812990209517091417)
                    ·
                      rfl

theorem cell23_5485152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_5485152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485152 prefixEnd_5485152 := by exact prefixLift 5485152
  have htrace : WordTrace (prefixWord ++ tailWord_5485152) baseStart_5485152 baseEnd_5485152 := by
    simpa [prefixWord, tailWord_5485152, baseEnd_5485152] using wordTrace_append hprefix tailTrace_5485152
  have hstable : (prefixWord ++ tailWord_5485152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485152).length < 2 ^ (prefixWord ++ tailWord_5485152).sum := by decide
  have hdescent : baseEnd_5485152 < baseStart_5485152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485153 : List Nat := [1, 2, 3, 1, 1, 5, 3, 2, 1, 1, 3]
def baseStart_5485153 : Nat := 118140960795 + 5485153 * 2 ^ 59
def prefixEnd_5485153 : Nat := 4983230072969 + 3 ^ 40 * 5485153 * 2
def baseEnd_5485153 : Nat := 2816519952451283047361747

theorem tailTrace_5485153 : CollatzResearch.WordTrace tailWord_5485153 prefixEnd_5485153 2816519952451283047361747 := by
  unfold tailWord_5485153
  simp only [CollatzResearch.WordTrace]
  refine ⟨200059965497234945395884113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133373310331489963597256075 200059965497234945395884113)
  ·
    refine ⟨150044974122926209046913085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200059965497234945395884113 150044974122926209046913085)
    ·
      refine ⟨56266865296097328392592407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150044974122926209046913085 56266865296097328392592407)
      ·
        refine ⟨84400297944145992588888611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56266865296097328392592407 84400297944145992588888611)
        ·
          refine ⟨126600446916218988883332917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84400297944145992588888611 126600446916218988883332917)
          ·
            refine ⟨11868791898395530207812461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126600446916218988883332917 11868791898395530207812461)
            ·
              refine ⟨4450796961898323827929673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11868791898395530207812461 4450796961898323827929673)
              ·
                refine ⟨3338097721423742870947255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4450796961898323827929673 3338097721423742870947255)
                ·
                  refine ⟨5007146582135614306420883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338097721423742870947255 5007146582135614306420883)
                  ·
                    refine ⟨7510719873203421459631325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5007146582135614306420883 7510719873203421459631325)
                    ·
                      refine ⟨2816519952451283047361747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7510719873203421459631325 2816519952451283047361747)
                      ·
                        rfl

theorem cell23_5485153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_5485153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485153 prefixEnd_5485153 := by exact prefixLift 5485153
  have htrace : WordTrace (prefixWord ++ tailWord_5485153) baseStart_5485153 baseEnd_5485153 := by
    simpa [prefixWord, tailWord_5485153, baseEnd_5485153] using wordTrace_append hprefix tailTrace_5485153
  have hstable : (prefixWord ++ tailWord_5485153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485153).length < 2 ^ (prefixWord ++ tailWord_5485153).sum := by decide
  have hdescent : baseEnd_5485153 < baseStart_5485153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485155 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6]
def baseStart_5485155 : Nat := 118140960795 + 5485155 * 2 ^ 59
def prefixEnd_5485155 : Nat := 4983230072969 + 3 ^ 40 * 5485155 * 2
def baseEnd_5485155 : Nat := 2816520979412592039536737

theorem tailTrace_5485155 : CollatzResearch.WordTrace tailWord_5485155 prefixEnd_5485155 2816520979412592039536737 := by
  unfold tailWord_5485155
  simp only [CollatzResearch.WordTrace]
  refine ⟨200060038443227699737456919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133373358962151799824971279 200060038443227699737456919)
  ·
    refine ⟨300090057664841549606185379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200060038443227699737456919 300090057664841549606185379)
    ·
      refine ⟨450135086497262324409278069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300090057664841549606185379 450135086497262324409278069)
      ·
        refine ⟨42200164359118342913369819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 450135086497262324409278069 42200164359118342913369819)
        ·
          refine ⟨63300246538677514370054729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42200164359118342913369819 63300246538677514370054729)
          ·
            refine ⟨47475184904008135777541047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63300246538677514370054729 47475184904008135777541047)
            ·
              refine ⟨71212777356012203666311571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47475184904008135777541047 71212777356012203666311571)
              ·
                refine ⟨106819166034018305499467357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71212777356012203666311571 106819166034018305499467357)
                ·
                  refine ⟨40057187262756864562300259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106819166034018305499467357 40057187262756864562300259)
                  ·
                    refine ⟨60085780894135296843450389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40057187262756864562300259 60085780894135296843450389)
                    ·
                      refine ⟨2816520979412592039536737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60085780894135296843450389 2816520979412592039536737)
                      ·
                        rfl

theorem cell23_5485155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_5485155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485155 prefixEnd_5485155 := by exact prefixLift 5485155
  have htrace : WordTrace (prefixWord ++ tailWord_5485155) baseStart_5485155 baseEnd_5485155 := by
    simpa [prefixWord, tailWord_5485155, baseEnd_5485155] using wordTrace_append hprefix tailTrace_5485155
  have hstable : (prefixWord ++ tailWord_5485155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485155).length < 2 ^ (prefixWord ++ tailWord_5485155).sum := by decide
  have hdescent : baseEnd_5485155 < baseStart_5485155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485162 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_5485162 : Nat := 118140960795 + 5485162 * 2 ^ 59
def prefixEnd_5485162 : Nat := 4983230072969 + 3 ^ 40 * 5485162 * 2
def baseEnd_5485162 : Nat := 2816524573777173512149205

theorem tailTrace_5485162 : CollatzResearch.WordTrace tailWord_5485162 prefixEnd_5485162 2816524573777173512149205 := by
  unfold tailWord_5485162
  simp only [CollatzResearch.WordTrace]
  refine ⟨50015073438550584983240435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133373529169468226621974493 50015073438550584983240435)
  ·
    refine ⟨75022610157825877474860653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50015073438550584983240435 75022610157825877474860653)
    ·
      refine ⟨28133478809184704053072745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75022610157825877474860653 28133478809184704053072745)
      ·
        refine ⟨21100109106888528039804559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28133478809184704053072745 21100109106888528039804559)
        ·
          refine ⟨31650163660332792059706839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21100109106888528039804559 31650163660332792059706839)
          ·
            refine ⟨47475245490499188089560259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31650163660332792059706839 47475245490499188089560259)
            ·
              refine ⟨71212868235748782134340389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47475245490499188089560259 71212868235748782134340389)
              ·
                refine ⟨13352412794202896650188823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71212868235748782134340389 13352412794202896650188823)
                ·
                  refine ⟨20028619191304344975283235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13352412794202896650188823 20028619191304344975283235)
                  ·
                    refine ⟨30042928786956517462924853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20028619191304344975283235 30042928786956517462924853)
                    ·
                      refine ⟨2816524573777173512149205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30042928786956517462924853 2816524573777173512149205)
                      ·
                        rfl

theorem cell23_5485162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_5485162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485162 prefixEnd_5485162 := by exact prefixLift 5485162
  have htrace : WordTrace (prefixWord ++ tailWord_5485162) baseStart_5485162 baseEnd_5485162 := by
    simpa [prefixWord, tailWord_5485162, baseEnd_5485162] using wordTrace_append hprefix tailTrace_5485162
  have hstable : (prefixWord ++ tailWord_5485162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485162).length < 2 ^ (prefixWord ++ tailWord_5485162).sum := by decide
  have hdescent : baseEnd_5485162 < baseStart_5485162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485173 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_5485173 : Nat := 118140960795 + 5485173 * 2 ^ 59
def prefixEnd_5485173 : Nat := 4983230072969 + 3 ^ 40 * 5485173 * 2
def baseEnd_5485173 : Nat := 938843407354790989703885

theorem tailTrace_5485173 : CollatzResearch.WordTrace tailWord_5485173 prefixEnd_5485173 938843407354790989703885 := by
  unfold tailWord_5485173
  simp only [CollatzResearch.WordTrace]
  refine ⟨200060694957162488811612173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133373796638108325874408115 200060694957162488811612173)
  ·
    refine ⟨75022760608935933304354565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200060694957162488811612173 75022760608935933304354565)
    ·
      refine ⟨14066767614175487494566481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75022760608935933304354565 14066767614175487494566481)
      ·
        refine ⟨10550075710631615620924861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14066767614175487494566481 10550075710631615620924861)
        ·
          refine ⟨3956278391486855857846823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10550075710631615620924861 3956278391486855857846823)
          ·
            refine ⟨5934417587230283786770235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956278391486855857846823 5934417587230283786770235)
            ·
              refine ⟨8901626380845425680155353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934417587230283786770235 8901626380845425680155353)
              ·
                refine ⟨6676219785634069260116515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8901626380845425680155353 6676219785634069260116515)
                ·
                  refine ⟨10014329678451103890174773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6676219785634069260116515 10014329678451103890174773)
                  ·
                    refine ⟨938843407354790989703885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10014329678451103890174773 938843407354790989703885)
                    ·
                      rfl

theorem cell23_5485173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_5485173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485173 prefixEnd_5485173 := by exact prefixLift 5485173
  have htrace : WordTrace (prefixWord ++ tailWord_5485173) baseStart_5485173 baseEnd_5485173 := by
    simpa [prefixWord, tailWord_5485173, baseEnd_5485173] using wordTrace_append hprefix tailTrace_5485173
  have hstable : (prefixWord ++ tailWord_5485173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485173).length < 2 ^ (prefixWord ++ tailWord_5485173).sum := by decide
  have hdescent : baseEnd_5485173 < baseStart_5485173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485205 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_5485205 : Nat := 118140960795 + 5485205 * 2 ^ 59
def prefixEnd_5485205 : Nat := 4983230072969 + 3 ^ 40 * 5485205 * 2
def baseEnd_5485205 : Nat := 2816546653445316843911507

theorem tailTrace_5485205 : CollatzResearch.WordTrace tailWord_5485205 prefixEnd_5485205 2816546653445316843911507 := by
  unfold tailWord_5485205
  simp only [CollatzResearch.WordTrace]
  refine ⟨200061862093046558276777069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133374574728697705517851379 200061862093046558276777069)
  ·
    refine ⟨75023198284892459353791401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200061862093046558276777069 75023198284892459353791401)
    ·
      refine ⟨56267398713669344515343551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75023198284892459353791401 56267398713669344515343551)
      ·
        refine ⟨84401098070504016773015327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56267398713669344515343551 84401098070504016773015327)
        ·
          refine ⟨126601647105756025159522991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84401098070504016773015327 126601647105756025159522991)
          ·
            refine ⟨189902470658634037739284487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126601647105756025159522991 189902470658634037739284487)
            ·
              refine ⟨284853705987951056608926731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189902470658634037739284487 284853705987951056608926731)
              ·
                refine ⟨427280558981926584913390097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284853705987951056608926731 427280558981926584913390097)
                ·
                  refine ⟨320460419236444938685042573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427280558981926584913390097 320460419236444938685042573)
                  ·
                    refine ⟨120172657213666852006890965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320460419236444938685042573 120172657213666852006890965)
                    ·
                      refine ⟨2816546653445316843911507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120172657213666852006890965 2816546653445316843911507)
                      ·
                        rfl

theorem cell23_5485205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_5485205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485205 prefixEnd_5485205 := by exact prefixLift 5485205
  have htrace : WordTrace (prefixWord ++ tailWord_5485205) baseStart_5485205 baseEnd_5485205 := by
    simpa [prefixWord, tailWord_5485205, baseEnd_5485205] using wordTrace_append hprefix tailTrace_5485205
  have hstable : (prefixWord ++ tailWord_5485205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485205).length < 2 ^ (prefixWord ++ tailWord_5485205).sum := by decide
  have hdescent : baseEnd_5485205 < baseStart_5485205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485212 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_5485212 : Nat := 118140960795 + 5485212 * 2 ^ 59
def prefixEnd_5485212 : Nat := 4983230072969 + 3 ^ 40 * 5485212 * 2
def baseEnd_5485212 : Nat := 938850082603299438841325

theorem tailTrace_5485212 : CollatzResearch.WordTrace tailWord_5485212 prefixEnd_5485212 938850082603299438841325 := by
  unfold tailWord_5485212
  simp only [CollatzResearch.WordTrace]
  refine ⟨100031058702010599236140945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133374744936014132314854593 100031058702010599236140945)
  ·
    refine ⟨75023294026507949427105709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100031058702010599236140945 75023294026507949427105709)
    ·
      refine ⟨28133735259940481035164641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75023294026507949427105709 28133735259940481035164641)
      ·
        refine ⟨21100301444955360776373481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28133735259940481035164641 21100301444955360776373481)
        ·
          refine ⟨15825226083716520582280111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21100301444955360776373481 15825226083716520582280111)
          ·
            refine ⟨23737839125574780873420167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15825226083716520582280111 23737839125574780873420167)
            ·
              refine ⟨35606758688362171310130251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23737839125574780873420167 35606758688362171310130251)
              ·
                refine ⟨53410138032543256965195377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35606758688362171310130251 53410138032543256965195377)
                ·
                  refine ⟨40057603524407442723896533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53410138032543256965195377 40057603524407442723896533)
                  ·
                    refine ⟨938850082603299438841325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40057603524407442723896533 938850082603299438841325)
                    ·
                      rfl

theorem cell23_5485212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_5485212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485212 prefixEnd_5485212 := by exact prefixLift 5485212
  have htrace : WordTrace (prefixWord ++ tailWord_5485212) baseStart_5485212 baseEnd_5485212 := by
    simpa [prefixWord, tailWord_5485212, baseEnd_5485212] using wordTrace_append hprefix tailTrace_5485212
  have hstable : (prefixWord ++ tailWord_5485212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485212).length < 2 ^ (prefixWord ++ tailWord_5485212).sum := by decide
  have hdescent : baseEnd_5485212 < baseStart_5485212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485225 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 1, 8]
def baseStart_5485225 : Nat := 118140960795 + 5485225 * 2 ^ 59
def prefixEnd_5485225 : Nat := 4983230072969 + 3 ^ 40 * 5485225 * 2
def baseEnd_5485225 : Nat := 938852307686135588553805

theorem tailTrace_5485225 : CollatzResearch.WordTrace tailWord_5485225 prefixEnd_5485225 938852307686135588553805 := by
  unfold tailWord_5485225
  simp only [CollatzResearch.WordTrace]
  refine ⟨200062591552974101692505129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133375061035316067795003419 200062591552974101692505129)
  ·
    refine ⟨150046943664730576269378847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200062591552974101692505129 150046943664730576269378847)
    ·
      refine ⟨225070415497095864404068271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150046943664730576269378847 225070415497095864404068271)
      ·
        refine ⟨337605623245643796606102407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225070415497095864404068271 337605623245643796606102407)
        ·
          refine ⟨506408434868465694909153611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337605623245643796606102407 506408434868465694909153611)
          ·
            refine ⟨759612652302698542363730417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506408434868465694909153611 759612652302698542363730417)
            ·
              refine ⟨569709489227023906772797813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759612652302698542363730417 569709489227023906772797813)
              ·
                refine ⟨53410264615033491259949795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 569709489227023906772797813 53410264615033491259949795)
                ·
                  refine ⟨80115396922550236889924693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53410264615033491259949795 80115396922550236889924693)
                  ·
                    refine ⟨938852307686135588553805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80115396922550236889924693 938852307686135588553805)
                    ·
                      rfl

theorem cell23_5485225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_5485225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485225 prefixEnd_5485225 := by exact prefixLift 5485225
  have htrace : WordTrace (prefixWord ++ tailWord_5485225) baseStart_5485225 baseEnd_5485225 := by
    simpa [prefixWord, tailWord_5485225, baseEnd_5485225] using wordTrace_append hprefix tailTrace_5485225
  have hstable : (prefixWord ++ tailWord_5485225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485225).length < 2 ^ (prefixWord ++ tailWord_5485225).sum := by decide
  have hdescent : baseEnd_5485225 < baseStart_5485225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485272 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 7]
def baseStart_5485272 : Nat := 118140960795 + 5485272 * 2 ^ 59
def prefixEnd_5485272 : Nat := 4983230072969 + 3 ^ 40 * 5485272 * 2
def baseEnd_5485272 : Nat := 312953450738796453530411

theorem tailTrace_5485272 : CollatzResearch.WordTrace tailWord_5485272 prefixEnd_5485272 312953450738796453530411 := by
  unfold tailWord_5485272
  simp only [CollatzResearch.WordTrace]
  refine ⟨100032152891901914359733035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133376203855869219146310713 100032152891901914359733035)
  ·
    refine ⟨150048229337852871539599553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100032152891901914359733035 150048229337852871539599553)
    ·
      refine ⟨112536172003389653654699665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150048229337852871539599553 112536172003389653654699665)
      ·
        refine ⟨84402129002542240241024749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112536172003389653654699665 84402129002542240241024749)
        ·
          refine ⟨31650798375953340090384281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84402129002542240241024749 31650798375953340090384281)
          ·
            refine ⟨23738098781965005067788211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31650798375953340090384281 23738098781965005067788211)
            ·
              refine ⟨35607148172947507601682317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23738098781965005067788211 35607148172947507601682317)
              ·
                refine ⟨13352680564855315350630869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35607148172947507601682317 13352680564855315350630869)
                ·
                  refine ⟨312953450738796453530411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13352680564855315350630869 312953450738796453530411)
                  ·
                    rfl

theorem cell23_5485272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 7].length) (baseStart_5485272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485272 prefixEnd_5485272 := by exact prefixLift 5485272
  have htrace : WordTrace (prefixWord ++ tailWord_5485272) baseStart_5485272 baseEnd_5485272 := by
    simpa [prefixWord, tailWord_5485272, baseEnd_5485272] using wordTrace_append hprefix tailTrace_5485272
  have hstable : (prefixWord ++ tailWord_5485272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485272).length < 2 ^ (prefixWord ++ tailWord_5485272).sum := by decide
  have hdescent : baseEnd_5485272 < baseStart_5485272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485283 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5485283 : Nat := 118140960795 + 5485283 * 2 ^ 59
def prefixEnd_5485283 : Nat := 4983230072969 + 3 ^ 40 * 5485283 * 2
def baseEnd_5485283 : Nat := 2816586704936367538736149

theorem tailTrace_5485283 : CollatzResearch.WordTrace tailWord_5485283 prefixEnd_5485283 2816586704936367538736149 := by
  unfold tailWord_5485283
  simp only [CollatzResearch.WordTrace]
  refine ⟨200064706986763977598116503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133376471324509318398744335 200064706986763977598116503)
  ·
    refine ⟨300097060480145966397174755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200064706986763977598116503 300097060480145966397174755)
    ·
      refine ⟨450145590720218949595762133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300097060480145966397174755 450145590720218949595762133)
      ·
        refine ⟨10550287282505131631150675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 450145590720218949595762133 10550287282505131631150675)
        ·
          refine ⟨15825430923757697446726013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10550287282505131631150675 15825430923757697446726013)
          ·
            refine ⟨5934536596409136542522255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15825430923757697446726013 5934536596409136542522255)
            ·
              refine ⟨8901804894613704813783383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934536596409136542522255 8901804894613704813783383)
              ·
                refine ⟨13352707341920557220675075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8901804894613704813783383 13352707341920557220675075)
                ·
                  refine ⟨20029061012880835831012613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13352707341920557220675075 20029061012880835831012613)
                  ·
                    refine ⟨3755448939915156718314865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20029061012880835831012613 3755448939915156718314865)
                    ·
                      refine ⟨2816586704936367538736149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755448939915156718314865 2816586704936367538736149)
                      ·
                        rfl

theorem cell23_5485283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5485283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485283 prefixEnd_5485283 := by exact prefixLift 5485283
  have htrace : WordTrace (prefixWord ++ tailWord_5485283) baseStart_5485283 baseEnd_5485283 := by
    simpa [prefixWord, tailWord_5485283, baseEnd_5485283] using wordTrace_append hprefix tailTrace_5485283
  have hstable : (prefixWord ++ tailWord_5485283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485283).length < 2 ^ (prefixWord ++ tailWord_5485283).sum := by decide
  have hdescent : baseEnd_5485283 < baseStart_5485283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485319 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 4, 5]
def baseStart_5485319 : Nat := 118140960795 + 5485319 * 2 ^ 59
def prefixEnd_5485319 : Nat := 4983230072969 + 3 ^ 40 * 5485319 * 2
def baseEnd_5485319 : Nat := 938868396746643132628661

theorem tailTrace_5485319 : CollatzResearch.WordTrace tailWord_5485319 prefixEnd_5485319 938868396746643132628661 := by
  unfold tailWord_5485319
  simp only [CollatzResearch.WordTrace]
  refine ⟨200066020014633555746427011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133377346676422370497618007 200066020014633555746427011)
  ·
    refine ⟨300099030021950333619640517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200066020014633555746427011 300099030021950333619640517)
    ·
      refine ⟨56268568129115687553682597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 300099030021950333619640517 56268568129115687553682597)
      ·
        refine ⟨10550356524209191416315487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56268568129115687553682597 10550356524209191416315487)
        ·
          refine ⟨15825534786313787124473231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10550356524209191416315487 15825534786313787124473231)
          ·
            refine ⟨23738302179470680686709847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15825534786313787124473231 23738302179470680686709847)
            ·
              refine ⟨35607453269206021030064771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23738302179470680686709847 35607453269206021030064771)
              ·
                refine ⟨53411179903809031545097157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35607453269206021030064771 53411179903809031545097157)
                ·
                  refine ⟨10014596231964193414705717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53411179903809031545097157 10014596231964193414705717)
                  ·
                    refine ⟨938868396746643132628661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10014596231964193414705717 938868396746643132628661)
                    ·
                      rfl

theorem cell23_5485319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_5485319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485319 prefixEnd_5485319 := by exact prefixLift 5485319
  have htrace : WordTrace (prefixWord ++ tailWord_5485319) baseStart_5485319 baseEnd_5485319 := by
    simpa [prefixWord, tailWord_5485319, baseEnd_5485319] using wordTrace_append hprefix tailTrace_5485319
  have hstable : (prefixWord ++ tailWord_5485319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485319).length < 2 ^ (prefixWord ++ tailWord_5485319).sum := by decide
  have hdescent : baseEnd_5485319 < baseStart_5485319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485349 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_5485349 : Nat := 118140960795 + 5485349 * 2 ^ 59
def prefixEnd_5485349 : Nat := 4983230072969 + 3 ^ 40 * 5485349 * 2
def baseEnd_5485349 : Nat := 938873531553188093503615

theorem tailTrace_5485349 : CollatzResearch.WordTrace tailWord_5485349 prefixEnd_5485349 938873531553188093503615 := by
  unfold tailWord_5485349
  simp only [CollatzResearch.WordTrace]
  refine ⟨200067114204524870870019101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133378076136349913913346067 200067114204524870870019101)
  ·
    refine ⟨75025167826696826576257163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200067114204524870870019101 75025167826696826576257163)
    ·
      refine ⟨112537751740045239864385745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75025167826696826576257163 112537751740045239864385745)
      ·
        refine ⟨84403313805033929898289309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112537751740045239864385745 84403313805033929898289309)
        ·
          refine ⟨31651242676887723711858491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84403313805033929898289309 31651242676887723711858491)
          ·
            refine ⟨47476864015331585567787737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31651242676887723711858491 47476864015331585567787737)
            ·
              refine ⟨35607648011498689175840803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47476864015331585567787737 35607648011498689175840803)
              ·
                refine ⟨53411472017248033763761205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35607648011498689175840803 53411472017248033763761205)
                ·
                  refine ⟨5007325501617003165352613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53411472017248033763761205 5007325501617003165352613)
                  ·
                    refine ⟨938873531553188093503615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007325501617003165352613 938873531553188093503615)
                    ·
                      rfl

theorem cell23_5485349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_5485349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485349 prefixEnd_5485349 := by exact prefixLift 5485349
  have htrace : WordTrace (prefixWord ++ tailWord_5485349) baseStart_5485349 baseEnd_5485349 := by
    simpa [prefixWord, tailWord_5485349, baseEnd_5485349] using wordTrace_append hprefix tailTrace_5485349
  have hstable : (prefixWord ++ tailWord_5485349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485349).length < 2 ^ (prefixWord ++ tailWord_5485349).sum := by decide
  have hdescent : baseEnd_5485349 < baseStart_5485349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485379 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 6]
def baseStart_5485379 : Nat := 118140960795 + 5485379 * 2 ^ 59
def prefixEnd_5485379 : Nat := 4983230072969 + 3 ^ 40 * 5485379 * 2
def baseEnd_5485379 : Nat := 312959555453244351459523

theorem tailTrace_5485379 : CollatzResearch.WordTrace tailWord_5485379 prefixEnd_5485379 312959555453244351459523 := by
  unfold tailWord_5485379
  simp only [CollatzResearch.WordTrace]
  refine ⟨200068208394416185993611191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133378805596277457329074127 200068208394416185993611191)
  ·
    refine ⟨300102312591624278990416787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200068208394416185993611191 300102312591624278990416787)
    ·
      refine ⟨450153468887436418485625181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300102312591624278990416787 450153468887436418485625181)
      ·
        refine ⟨168807550832788656932109443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450153468887436418485625181 168807550832788656932109443)
        ·
          refine ⟨253211326249182985398164165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168807550832788656932109443 253211326249182985398164165)
          ·
            refine ⟨47477123671721809762155781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253211326249182985398164165 47477123671721809762155781)
            ·
              refine ⟨8901960688447839330404209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47477123671721809762155781 8901960688447839330404209)
              ·
                refine ⟨6676470516335879497803157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8901960688447839330404209 6676470516335879497803157)
                ·
                  refine ⟨312959555453244351459523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6676470516335879497803157 312959555453244351459523)
                  ·
                    rfl

theorem cell23_5485379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 6].length) (baseStart_5485379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485379 prefixEnd_5485379 := by exact prefixLift 5485379
  have htrace : WordTrace (prefixWord ++ tailWord_5485379) baseStart_5485379 baseEnd_5485379 := by
    simpa [prefixWord, tailWord_5485379, baseEnd_5485379] using wordTrace_append hprefix tailTrace_5485379
  have hstable : (prefixWord ++ tailWord_5485379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485379).length < 2 ^ (prefixWord ++ tailWord_5485379).sum := by decide
  have hdescent : baseEnd_5485379 < baseStart_5485379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485410 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_5485410 : Nat := 118140960795 + 5485410 * 2 ^ 59
def prefixEnd_5485410 : Nat := 4983230072969 + 3 ^ 40 * 5485410 * 2
def baseEnd_5485410 : Nat := 2816651916979488541848065

theorem tailTrace_5485410 : CollatzResearch.WordTrace tailWord_5485410 prefixEnd_5485410 2816651916979488541848065 := by
  unfold tailWord_5485410
  simp only [CollatzResearch.WordTrace]
  refine ⟨50017334764325969571997421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133379559371535918858659789 50017334764325969571997421)
  ·
    refine ⟨18756500536622238589499033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50017334764325969571997421 18756500536622238589499033)
    ·
      refine ⟨14067375402466678942124275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18756500536622238589499033 14067375402466678942124275)
      ·
        refine ⟨21101063103700018413186413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14067375402466678942124275 21101063103700018413186413)
        ·
          refine ⟨7912898663887506904944905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21101063103700018413186413 7912898663887506904944905)
          ·
            refine ⟨5934673997915630178708679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7912898663887506904944905 5934673997915630178708679)
            ·
              refine ⟨8902010996873445268063019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934673997915630178708679 8902010996873445268063019)
              ·
                refine ⟨13353016495310167902094529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8902010996873445268063019 13353016495310167902094529)
                ·
                  refine ⟨10014762371482625926570897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13353016495310167902094529 10014762371482625926570897)
                  ·
                    refine ⟨7511071778611969444928173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10014762371482625926570897 7511071778611969444928173)
                    ·
                      refine ⟨2816651916979488541848065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7511071778611969444928173 2816651916979488541848065)
                      ·
                        rfl

theorem cell23_5485410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_5485410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485410 prefixEnd_5485410 := by exact prefixLift 5485410
  have htrace : WordTrace (prefixWord ++ tailWord_5485410) baseStart_5485410 baseEnd_5485410 := by
    simpa [prefixWord, tailWord_5485410, baseEnd_5485410] using wordTrace_append hprefix tailTrace_5485410
  have hstable : (prefixWord ++ tailWord_5485410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485410).length < 2 ^ (prefixWord ++ tailWord_5485410).sum := by decide
  have hdescent : baseEnd_5485410 < baseStart_5485410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485449 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_5485449 : Nat := 118140960795 + 5485449 * 2 ^ 59
def prefixEnd_5485449 : Nat := 4983230072969 + 3 ^ 40 * 5485449 * 2
def baseEnd_5485449 : Nat := 2816671942725013889260385

theorem tailTrace_5485449 : CollatzResearch.WordTrace tailWord_5485449 prefixEnd_5485449 2816671942725013889260385 := by
  unfold tailWord_5485449
  simp only [CollatzResearch.WordTrace]
  refine ⟨200070761504162587948659401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133380507669441725299106267 200070761504162587948659401)
  ·
    refine ⟨150053071128121940961494551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200070761504162587948659401 150053071128121940961494551)
    ·
      refine ⟨225079606692182911442241827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150053071128121940961494551 225079606692182911442241827)
      ·
        refine ⟨337619410038274367163362741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225079606692182911442241827 337619410038274367163362741)
        ·
          refine ⟨31651819691088221921565257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 337619410038274367163362741 31651819691088221921565257)
          ·
            refine ⟨23738864768316166441173943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31651819691088221921565257 23738864768316166441173943)
            ·
              refine ⟨35608297152474249661760915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23738864768316166441173943 35608297152474249661760915)
              ·
                refine ⟨53412445728711374492641373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35608297152474249661760915 53412445728711374492641373)
                ·
                  refine ⟨20029667148266765434740515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53412445728711374492641373 20029667148266765434740515)
                  ·
                    refine ⟨30044500722400148152110773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20029667148266765434740515 30044500722400148152110773)
                    ·
                      refine ⟨2816671942725013889260385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30044500722400148152110773 2816671942725013889260385)
                      ·
                        rfl

theorem cell23_5485449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_5485449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485449 prefixEnd_5485449 := by exact prefixLift 5485449
  have htrace : WordTrace (prefixWord ++ tailWord_5485449) baseStart_5485449 baseEnd_5485449 := by
    simpa [prefixWord, tailWord_5485449, baseEnd_5485449] using wordTrace_append hprefix tailTrace_5485449
  have hstable : (prefixWord ++ tailWord_5485449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485449).length < 2 ^ (prefixWord ++ tailWord_5485449).sum := by decide
  have hdescent : baseEnd_5485449 < baseStart_5485449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485459 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4]
def baseStart_5485459 : Nat := 118140960795 + 5485459 * 2 ^ 59
def prefixEnd_5485459 : Nat := 4983230072969 + 3 ^ 40 * 5485459 * 2
def baseEnd_5485459 : Nat := 2816677077531558850135339

theorem tailTrace_5485459 : CollatzResearch.WordTrace tailWord_5485459 prefixEnd_5485459 2816677077531558850135339 := by
  unfold tailWord_5485459
  simp only [CollatzResearch.WordTrace]
  refine ⟨200071126234126359656523431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133380750822750906437682287 200071126234126359656523431)
  ·
    refine ⟨300106689351189539484785147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200071126234126359656523431 300106689351189539484785147)
    ·
      refine ⟨450160034026784309227177721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300106689351189539484785147 450160034026784309227177721)
      ·
        refine ⟨337620025520088231920383291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450160034026784309227177721 337620025520088231920383291)
        ·
          refine ⟨506430038280132347880574937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337620025520088231920383291 506430038280132347880574937)
          ·
            refine ⟨379822528710099260910431203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506430038280132347880574937 379822528710099260910431203)
            ·
              refine ⟨569733793065148891365646805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379822528710099260910431203 569733793065148891365646805)
              ·
                refine ⟨13353135774964427141382347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 569733793065148891365646805 13353135774964427141382347)
                ·
                  refine ⟨20029703662446640712073521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13353135774964427141382347 20029703662446640712073521)
                  ·
                    refine ⟨15022277746834980534055141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20029703662446640712073521 15022277746834980534055141)
                    ·
                      refine ⟨2816677077531558850135339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15022277746834980534055141 2816677077531558850135339)
                      ·
                        rfl

theorem cell23_5485459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_5485459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485459 prefixEnd_5485459 := by exact prefixLift 5485459
  have htrace : WordTrace (prefixWord ++ tailWord_5485459) baseStart_5485459 baseEnd_5485459 := by
    simpa [prefixWord, tailWord_5485459, baseEnd_5485459] using wordTrace_append hprefix tailTrace_5485459
  have hstable : (prefixWord ++ tailWord_5485459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485459).length < 2 ^ (prefixWord ++ tailWord_5485459).sum := by decide
  have hdescent : baseEnd_5485459 < baseStart_5485459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485463 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 3, 2, 2]
def baseStart_5485463 : Nat := 118140960795 + 5485463 * 2 ^ 59
def prefixEnd_5485463 : Nat := 4983230072969 + 3 ^ 40 * 5485463 * 2
def baseEnd_5485463 : Nat := 2816679131454176834485321

theorem tailTrace_5485463 : CollatzResearch.WordTrace tailWord_5485463 prefixEnd_5485463 2816679131454176834485321 := by
  unfold tailWord_5485463
  simp only [CollatzResearch.WordTrace]
  refine ⟨200071272126111868339669043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133380848084074578893112695 200071272126111868339669043)
  ·
    refine ⟨300106908189167802509503565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200071272126111868339669043 300106908189167802509503565)
    ·
      refine ⟨112540090570937925941063837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300106908189167802509503565 112540090570937925941063837)
      ·
        refine ⟨42202533964101722227898939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112540090570937925941063837 42202533964101722227898939)
        ·
          refine ⟨63303800946152583341848409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42202533964101722227898939 63303800946152583341848409)
          ·
            refine ⟨47477850709614437506386307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63303800946152583341848409 47477850709614437506386307)
            ·
              refine ⟨71216776064421656259579461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47477850709614437506386307 71216776064421656259579461)
              ·
                refine ⟨13353145512079060548671149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71216776064421656259579461 13353145512079060548671149)
                ·
                  refine ⟨5007429567029647705751681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13353145512079060548671149 5007429567029647705751681)
                  ·
                    refine ⟨3755572175272235779313761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5007429567029647705751681 3755572175272235779313761)
                    ·
                      refine ⟨2816679131454176834485321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755572175272235779313761 2816679131454176834485321)
                      ·
                        rfl

theorem cell23_5485463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_5485463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485463 prefixEnd_5485463 := by exact prefixLift 5485463
  have htrace : WordTrace (prefixWord ++ tailWord_5485463) baseStart_5485463 baseEnd_5485463 := by
    simpa [prefixWord, tailWord_5485463, baseEnd_5485463] using wordTrace_append hprefix tailTrace_5485463
  have hstable : (prefixWord ++ tailWord_5485463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485463).length < 2 ^ (prefixWord ++ tailWord_5485463).sum := by decide
  have hdescent : baseEnd_5485463 < baseStart_5485463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485469 : List Nat := [1, 4, 2, 1, 2, 1, 3, 9]
def baseStart_5485469 : Nat := 118140960795 + 5485469 * 2 ^ 59
def prefixEnd_5485469 : Nat := 4983230072969 + 3 ^ 40 * 5485469 * 2
def baseEnd_5485469 : Nat := 104321563419929770778159

theorem tailTrace_5485469 : CollatzResearch.WordTrace tailWord_5485469 prefixEnd_5485469 104321563419929770778159 := by
  unfold tailWord_5485469
  simp only [CollatzResearch.WordTrace]
  refine ⟨200071490964090131364387461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133380993976060087576258307 200071490964090131364387461)
  ·
    refine ⟨37513404555766899630822649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200071490964090131364387461 37513404555766899630822649)
    ·
      refine ⟨28135053416825174723116987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37513404555766899630822649 28135053416825174723116987)
      ·
        refine ⟨42202580125237762084675481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28135053416825174723116987 42202580125237762084675481)
        ·
          refine ⟨31651935093928321563506611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42202580125237762084675481 31651935093928321563506611)
          ·
            refine ⟨47477902640892482345259917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31651935093928321563506611 47477902640892482345259917)
            ·
              refine ⟨17804213490334680879472469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47477902640892482345259917 17804213490334680879472469)
              ·
                refine ⟨104321563419929770778159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17804213490334680879472469 104321563419929770778159)
                ·
                  rfl

theorem cell23_5485469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 9].length) (baseStart_5485469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485469 prefixEnd_5485469 := by exact prefixLift 5485469
  have htrace : WordTrace (prefixWord ++ tailWord_5485469) baseStart_5485469 baseEnd_5485469 := by
    simpa [prefixWord, tailWord_5485469, baseEnd_5485469] using wordTrace_append hprefix tailTrace_5485469
  have hstable : (prefixWord ++ tailWord_5485469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485469).length < 2 ^ (prefixWord ++ tailWord_5485469).sum := by decide
  have hdescent : baseEnd_5485469 < baseStart_5485469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485576 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 7]
def baseStart_5485576 : Nat := 118140960795 + 5485576 * 2 ^ 59
def prefixEnd_5485576 : Nat := 4983230072969 + 3 ^ 40 * 5485576 * 2
def baseEnd_5485576 : Nat := 312970794974237210263589

theorem tailTrace_5485576 : CollatzResearch.WordTrace tailWord_5485576 prefixEnd_5485576 312970794974237210263589 := by
  unfold tailWord_5485576
  simp only [CollatzResearch.WordTrace]
  refine ⟨100037696787351244319266291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133383595716468325759021721 100037696787351244319266291)
  ·
    refine ⟨150056545181026866478899437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100037696787351244319266291 150056545181026866478899437)
    ·
      refine ⟨56271204442885074929587289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150056545181026866478899437 56271204442885074929587289)
      ·
        refine ⟨42203403332163806197190467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56271204442885074929587289 42203403332163806197190467)
        ·
          refine ⟨63305104998245709295785701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42203403332163806197190467 63305104998245709295785701)
          ·
            refine ⟨11869707187171070492959819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63305104998245709295785701 11869707187171070492959819)
            ·
              refine ⟨17804560780756605739439729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11869707187171070492959819 17804560780756605739439729)
              ·
                refine ⟨13353420585567454304579797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17804560780756605739439729 13353420585567454304579797)
                ·
                  refine ⟨312970794974237210263589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13353420585567454304579797 312970794974237210263589)
                  ·
                    rfl

theorem cell23_5485576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 7].length) (baseStart_5485576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485576 prefixEnd_5485576 := by exact prefixLift 5485576
  have htrace : WordTrace (prefixWord ++ tailWord_5485576) baseStart_5485576 baseEnd_5485576 := by
    simpa [prefixWord, tailWord_5485576, baseEnd_5485576] using wordTrace_append hprefix tailTrace_5485576
  have hstable : (prefixWord ++ tailWord_5485576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485576).length < 2 ^ (prefixWord ++ tailWord_5485576).sum := by decide
  have hdescent : baseEnd_5485576 < baseStart_5485576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485604 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_5485604 : Nat := 118140960795 + 5485604 * 2 ^ 59
def prefixEnd_5485604 : Nat := 4983230072969 + 3 ^ 40 * 5485604 * 2
def baseEnd_5485604 : Nat := 2816751532226460782822173

theorem tailTrace_5485604 : CollatzResearch.WordTrace tailWord_5485604 prefixEnd_5485604 2816751532226460782822173 := by
  unfold tailWord_5485604
  simp only [CollatzResearch.WordTrace]
  refine ⟨100038207409300524710275933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133384276545734032947034577 100038207409300524710275933)
  ·
    refine ⟨37514327778487696766353475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100038207409300524710275933 37514327778487696766353475)
    ·
      refine ⟨56271491667731545149530213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37514327778487696766353475 56271491667731545149530213)
      ·
        refine ⟨10550904687699664715536915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56271491667731545149530213 10550904687699664715536915)
        ·
          refine ⟨15826357031549497073305373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10550904687699664715536915 15826357031549497073305373)
          ·
            refine ⟨5934883886831061402489515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15826357031549497073305373 5934883886831061402489515)
            ·
              refine ⟨8902325830246592103734273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5934883886831061402489515 8902325830246592103734273)
              ·
                refine ⟨6676744372684944077800705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8902325830246592103734273 6676744372684944077800705)
                ·
                  refine ⟨5007558279513708058350529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6676744372684944077800705 5007558279513708058350529)
                  ·
                    refine ⟨3755668709635281043762897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5007558279513708058350529 3755668709635281043762897)
                    ·
                      refine ⟨2816751532226460782822173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755668709635281043762897 2816751532226460782822173)
                      ·
                        rfl

theorem cell23_5485604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_5485604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485604 prefixEnd_5485604 := by exact prefixLift 5485604
  have htrace : WordTrace (prefixWord ++ tailWord_5485604) baseStart_5485604 baseEnd_5485604 := by
    simpa [prefixWord, tailWord_5485604, baseEnd_5485604] using wordTrace_append hprefix tailTrace_5485604
  have hstable : (prefixWord ++ tailWord_5485604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485604).length < 2 ^ (prefixWord ++ tailWord_5485604).sum := by decide
  have hdescent : baseEnd_5485604 < baseStart_5485604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485620 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5485620 : Nat := 118140960795 + 5485620 * 2 ^ 59
def prefixEnd_5485620 : Nat := 4983230072969 + 3 ^ 40 * 5485620 * 2
def baseEnd_5485620 : Nat := 2816759747916932720222099

theorem tailTrace_5485620 : CollatzResearch.WordTrace tailWord_5485620 prefixEnd_5485620 2816759747916932720222099 := by
  unfold tailWord_5485620
  simp only [CollatzResearch.WordTrace]
  refine ⟨100038499193271542076567157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133384665591028722768756209 100038499193271542076567157)
  ·
    refine ⟨9378609299369207069678171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100038499193271542076567157 9378609299369207069678171)
    ·
      refine ⟨14067913949053810604517257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9378609299369207069678171 14067913949053810604517257)
      ·
        refine ⟨10550935461790357953387943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14067913949053810604517257 10550935461790357953387943)
        ·
          refine ⟨15826403192685536930081915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10550935461790357953387943 15826403192685536930081915)
          ·
            refine ⟨23739604789028305395122873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15826403192685536930081915 23739604789028305395122873)
            ·
              refine ⟨17804703591771229046342155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23739604789028305395122873 17804703591771229046342155)
              ·
                refine ⟨26707055387656843569513233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17804703591771229046342155 26707055387656843569513233)
                ·
                  refine ⟨20030291540742632677134925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26707055387656843569513233 20030291540742632677134925)
                  ·
                    refine ⟨7511359327778487253925597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20030291540742632677134925 7511359327778487253925597)
                    ·
                      refine ⟨2816759747916932720222099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7511359327778487253925597 2816759747916932720222099)
                      ·
                        rfl

theorem cell23_5485620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5485620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485620 prefixEnd_5485620 := by exact prefixLift 5485620
  have htrace : WordTrace (prefixWord ++ tailWord_5485620) baseStart_5485620 baseEnd_5485620 := by
    simpa [prefixWord, tailWord_5485620, baseEnd_5485620] using wordTrace_append hprefix tailTrace_5485620
  have hstable : (prefixWord ++ tailWord_5485620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485620).length < 2 ^ (prefixWord ++ tailWord_5485620).sum := by decide
  have hdescent : baseEnd_5485620 < baseStart_5485620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485626 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_5485626 : Nat := 118140960795 + 5485626 * 2 ^ 59
def prefixEnd_5485626 : Nat := 4983230072969 + 3 ^ 40 * 5485626 * 2
def baseEnd_5485626 : Nat := 2816762828800859696747071

theorem tailTrace_5485626 : CollatzResearch.WordTrace tailWord_5485626 prefixEnd_5485626 2816762828800859696747071 := by
  unfold tailWord_5485626
  simp only [CollatzResearch.WordTrace]
  refine ⟨50019304306130336794463183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133384811483014231451901821 50019304306130336794463183)
  ·
    refine ⟨75028956459195505191694775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50019304306130336794463183 75028956459195505191694775)
    ·
      refine ⟨112543434688793257787542163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75028956459195505191694775 112543434688793257787542163)
      ·
        refine ⟨168815152033189886681313245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112543434688793257787542163 168815152033189886681313245)
        ·
          refine ⟨63305682012446207505492467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168815152033189886681313245 63305682012446207505492467)
          ·
            refine ⟨94958523018669311258238701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63305682012446207505492467 94958523018669311258238701)
            ·
              refine ⟨35609446132000991721839513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94958523018669311258238701 35609446132000991721839513)
              ·
                refine ⟨26707084599000743791379635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35609446132000991721839513 26707084599000743791379635)
                ·
                  refine ⟨40060626898501115687069453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26707084599000743791379635 40060626898501115687069453)
                  ·
                    refine ⟨15022735086937918382651045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40060626898501115687069453 15022735086937918382651045)
                    ·
                      refine ⟨2816762828800859696747071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15022735086937918382651045 2816762828800859696747071)
                      ·
                        rfl

theorem cell23_5485626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_5485626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485626 prefixEnd_5485626 := by exact prefixLift 5485626
  have htrace : WordTrace (prefixWord ++ tailWord_5485626) baseStart_5485626 baseEnd_5485626 := by
    simpa [prefixWord, tailWord_5485626, baseEnd_5485626] using wordTrace_append hprefix tailTrace_5485626
  have hstable : (prefixWord ++ tailWord_5485626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485626).length < 2 ^ (prefixWord ++ tailWord_5485626).sum := by decide
  have hdescent : baseEnd_5485626 < baseStart_5485626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485663 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 3]
def baseStart_5485663 : Nat := 118140960795 + 5485663 * 2 ^ 59
def prefixEnd_5485663 : Nat := 4983230072969 + 3 ^ 40 * 5485663 * 2
def baseEnd_5485663 : Nat := 2816781827585076051984401

theorem tailTrace_5485663 : CollatzResearch.WordTrace tailWord_5485663 prefixEnd_5485663 2816781827585076051984401 := by
  unfold tailWord_5485663
  simp only [CollatzResearch.WordTrace]
  refine ⟨200078566725387302496949643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133385711150258201664633095 200078566725387302496949643)
  ·
    refine ⟨300117850088080953745424465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200078566725387302496949643 300117850088080953745424465)
    ·
      refine ⟨225088387566060715309068349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300117850088080953745424465 225088387566060715309068349)
      ·
        refine ⟨84408145337272768240900631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225088387566060715309068349 84408145337272768240900631)
        ·
          refine ⟨126612218005909152361350947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84408145337272768240900631 126612218005909152361350947)
          ·
            refine ⟨189918327008863728542026421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126612218005909152361350947 189918327008863728542026421)
            ·
              refine ⟨17804843157080974550814977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189918327008863728542026421 17804843157080974550814977)
              ·
                refine ⟨13353632367810730913111233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17804843157080974550814977 13353632367810730913111233)
                ·
                  refine ⟨10015224275858048184833425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13353632367810730913111233 10015224275858048184833425)
                  ·
                    refine ⟨7511418206893536138625069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10015224275858048184833425 7511418206893536138625069)
                    ·
                      refine ⟨2816781827585076051984401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7511418206893536138625069 2816781827585076051984401)
                      ·
                        rfl

theorem cell23_5485663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_5485663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485663 prefixEnd_5485663 := by exact prefixLift 5485663
  have htrace : WordTrace (prefixWord ++ tailWord_5485663) baseStart_5485663 baseEnd_5485663 := by
    simpa [prefixWord, tailWord_5485663, baseEnd_5485663] using wordTrace_append hprefix tailTrace_5485663
  have hstable : (prefixWord ++ tailWord_5485663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485663).length < 2 ^ (prefixWord ++ tailWord_5485663).sum := by decide
  have hdescent : baseEnd_5485663 < baseStart_5485663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485733 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_5485733 : Nat := 118140960795 + 5485733 * 2 ^ 59
def prefixEnd_5485733 : Nat := 4983230072969 + 3 ^ 40 * 5485733 * 2
def baseEnd_5485733 : Nat := 2816817771230890778109079

theorem tailTrace_5485733 : CollatzResearch.WordTrace tailWord_5485733 prefixEnd_5485733 2816817771230890778109079 := by
  unfold tailWord_5485733
  simp only [CollatzResearch.WordTrace]
  refine ⟨200081119835133704451997853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133387413223422469634665235 200081119835133704451997853)
  ·
    refine ⟨75030419938175139169499195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200081119835133704451997853 75030419938175139169499195)
    ·
      refine ⟨112545629907262708754248793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75030419938175139169499195 112545629907262708754248793)
      ·
        refine ⟨84409222430447031565686595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112545629907262708754248793 84409222430447031565686595)
        ·
          refine ⟨126613833645670547348529893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84409222430447031565686595 126613833645670547348529893)
          ·
            refine ⟨23740093808563227627849355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126613833645670547348529893 23740093808563227627849355)
            ·
              refine ⟨35610140712844841441774033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23740093808563227627849355 35610140712844841441774033)
              ·
                refine ⟨26707605534633631081330525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35610140712844841441774033 26707605534633631081330525)
                ·
                  refine ⟨10015352075487611655498947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26707605534633631081330525 10015352075487611655498947)
                  ·
                    refine ⟨15023028113231417483248421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10015352075487611655498947 15023028113231417483248421)
                    ·
                      refine ⟨2816817771230890778109079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15023028113231417483248421 2816817771230890778109079)
                      ·
                        rfl

theorem cell23_5485733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_5485733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485733 prefixEnd_5485733 := by exact prefixLift 5485733
  have htrace : WordTrace (prefixWord ++ tailWord_5485733) baseStart_5485733 baseEnd_5485733 := by
    simpa [prefixWord, tailWord_5485733, baseEnd_5485733] using wordTrace_append hprefix tailTrace_5485733
  have hstable : (prefixWord ++ tailWord_5485733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485733).length < 2 ^ (prefixWord ++ tailWord_5485733).sum := by decide
  have hdescent : baseEnd_5485733 < baseStart_5485733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485761 : List Nat := [1, 2, 6, 1, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5485761 : Nat := 118140960795 + 5485761 * 2 ^ 59
def prefixEnd_5485761 : Nat := 4983230072969 + 3 ^ 40 * 5485761 * 2
def baseEnd_5485761 : Nat := 2816832148689216668558951

theorem tailTrace_5485761 : CollatzResearch.WordTrace tailWord_5485761 prefixEnd_5485761 2816832148689216668558951 := by
  unfold tailWord_5485761
  simp only [CollatzResearch.WordTrace]
  refine ⟨200082141079032265234017137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133388094052688176822678091 200082141079032265234017137)
  ·
    refine ⟨150061605809274198925512853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200082141079032265234017137 150061605809274198925512853)
    ·
      refine ⟨7034137772309728074633415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150061605809274198925512853 7034137772309728074633415)
      ·
        refine ⟨10551206658464592111950123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7034137772309728074633415 10551206658464592111950123)
        ·
          refine ⟨15826809987696888167925185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10551206658464592111950123 15826809987696888167925185)
          ·
            refine ⟨11870107490772666125943889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15826809987696888167925185 11870107490772666125943889)
            ·
              refine ⟨8902580618079499594457917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11870107490772666125943889 8902580618079499594457917)
              ·
                refine ⟨3338467731779812347921719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8902580618079499594457917 3338467731779812347921719)
                ·
                  refine ⟨5007701597669718521882579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338467731779812347921719 5007701597669718521882579)
                  ·
                    refine ⟨7511552396504577782823869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5007701597669718521882579 7511552396504577782823869)
                    ·
                      refine ⟨2816832148689216668558951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7511552396504577782823869 2816832148689216668558951)
                      ·
                        rfl

theorem cell23_5485761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5485761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485761 prefixEnd_5485761 := by exact prefixLift 5485761
  have htrace : WordTrace (prefixWord ++ tailWord_5485761) baseStart_5485761 baseEnd_5485761 := by
    simpa [prefixWord, tailWord_5485761, baseEnd_5485761] using wordTrace_append hprefix tailTrace_5485761
  have hstable : (prefixWord ++ tailWord_5485761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485761).length < 2 ^ (prefixWord ++ tailWord_5485761).sum := by decide
  have hdescent : baseEnd_5485761 < baseStart_5485761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485764 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_5485764 : Nat := 118140960795 + 5485764 * 2 ^ 59
def prefixEnd_5485764 : Nat := 4983230072969 + 3 ^ 40 * 5485764 * 2
def baseEnd_5485764 : Nat := 938944563043726718940479

theorem tailTrace_5485764 : CollatzResearch.WordTrace tailWord_5485764 prefixEnd_5485764 938944563043726718940479 := by
  unfold tailWord_5485764
  simp only [CollatzResearch.WordTrace]
  refine ⟨100041125249010698373188173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133388166998680931164250897 100041125249010698373188173)
  ·
    refine ⟨37515421968379011889945565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100041125249010698373188173 37515421968379011889945565)
    ·
      refine ⟨14068283238142129458729587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37515421968379011889945565 14068283238142129458729587)
      ·
        refine ⟨21102424857213194188094381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14068283238142129458729587 21102424857213194188094381)
        ·
          refine ⟨7913409321454947820535393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21102424857213194188094381 7913409321454947820535393)
          ·
            refine ⟨5935056991091210865401545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7913409321454947820535393 5935056991091210865401545)
            ·
              refine ⟨4451292743318408149051159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5935056991091210865401545 4451292743318408149051159)
              ·
                refine ⟨6676939114977612223576739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4451292743318408149051159 6676939114977612223576739)
                ·
                  refine ⟨10015408672466418335365109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6676939114977612223576739 10015408672466418335365109)
                  ·
                    refine ⟨938944563043726718940479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10015408672466418335365109 938944563043726718940479)
                    ·
                      rfl

theorem cell23_5485764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_5485764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485764 prefixEnd_5485764 := by exact prefixLift 5485764
  have htrace : WordTrace (prefixWord ++ tailWord_5485764) baseStart_5485764 baseEnd_5485764 := by
    simpa [prefixWord, tailWord_5485764, baseEnd_5485764] using wordTrace_append hprefix tailTrace_5485764
  have hstable : (prefixWord ++ tailWord_5485764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485764).length < 2 ^ (prefixWord ++ tailWord_5485764).sum := by decide
  have hdescent : baseEnd_5485764 < baseStart_5485764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485783 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_5485783 : Nat := 118140960795 + 5485783 * 2 ^ 59
def prefixEnd_5485783 : Nat := 4983230072969 + 3 ^ 40 * 5485783 * 2
def baseEnd_5485783 : Nat := 2816843445263615582483849

theorem tailTrace_5485783 : CollatzResearch.WordTrace tailWord_5485783 prefixEnd_5485783 2816843445263615582483849 := by
  unfold tailWord_5485783
  simp only [CollatzResearch.WordTrace]
  refine ⟨200082943484952562991318003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133388628989968375327545335 200082943484952562991318003)
  ·
    refine ⟨300124415227428844486977005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200082943484952562991318003 300124415227428844486977005)
    ·
      refine ⟨112546655710285816682616377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300124415227428844486977005 112546655710285816682616377)
      ·
        refine ⟨84409991782714362511962283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112546655710285816682616377 84409991782714362511962283)
        ·
          refine ⟨126614987674071543767943425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84409991782714362511962283 126614987674071543767943425)
          ·
            refine ⟨94961240755553657825957569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126614987674071543767943425 94961240755553657825957569)
            ·
              refine ⟨71220930566665243369468177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94961240755553657825957569 71220930566665243369468177)
              ·
                refine ⟨53415697924998932527101133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71220930566665243369468177 53415697924998932527101133)
                ·
                  refine ⟨20030886721874599697662925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53415697924998932527101133 20030886721874599697662925)
                  ·
                    refine ⟨7511582520702974886623597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20030886721874599697662925 7511582520702974886623597)
                    ·
                      refine ⟨2816843445263615582483849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7511582520702974886623597 2816843445263615582483849)
                      ·
                        rfl

theorem cell23_5485783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_5485783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485783 prefixEnd_5485783 := by exact prefixLift 5485783
  have htrace : WordTrace (prefixWord ++ tailWord_5485783) baseStart_5485783 baseEnd_5485783 := by
    simpa [prefixWord, tailWord_5485783, baseEnd_5485783] using wordTrace_append hprefix tailTrace_5485783
  have hstable : (prefixWord ++ tailWord_5485783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485783).length < 2 ^ (prefixWord ++ tailWord_5485783).sum := by decide
  have hdescent : baseEnd_5485783 < baseStart_5485783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485784 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 3, 2, 2]
def baseStart_5485784 : Nat := 118140960795 + 5485784 * 2 ^ 59
def prefixEnd_5485784 : Nat := 4983230072969 + 3 ^ 40 * 5485784 * 2
def baseEnd_5485784 : Nat := 2816843958744270078571345

theorem tailTrace_5485784 : CollatzResearch.WordTrace tailWord_5485784 prefixEnd_5485784 2816843958744270078571345 := by
  unfold tailWord_5485784
  simp only [CollatzResearch.WordTrace]
  refine ⟨100041489978974470081052203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133388653305299293441402937 100041489978974470081052203)
  ·
    refine ⟨150062234968461705121578305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100041489978974470081052203 150062234968461705121578305)
    ·
      refine ⟨112546676226346278841183729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150062234968461705121578305 112546676226346278841183729)
      ·
        refine ⟨84410007169759709130887797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112546676226346278841183729 84410007169759709130887797)
        ·
          refine ⟨7913438172164972731020731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84410007169759709130887797 7913438172164972731020731)
          ·
            refine ⟨11870157258247459096531097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7913438172164972731020731 11870157258247459096531097)
            ·
              refine ⟨8902617943685594322398323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11870157258247459096531097 8902617943685594322398323)
              ·
                refine ⟨13353926915528391483597485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8902617943685594322398323 13353926915528391483597485)
                ·
                  refine ⟨5007722593323146806349057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13353926915528391483597485 5007722593323146806349057)
                  ·
                    refine ⟨3755791944992360104761793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5007722593323146806349057 3755791944992360104761793)
                    ·
                      refine ⟨2816843958744270078571345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755791944992360104761793 2816843958744270078571345)
                      ·
                        rfl

theorem cell23_5485784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_5485784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485784 prefixEnd_5485784 := by exact prefixLift 5485784
  have htrace : WordTrace (prefixWord ++ tailWord_5485784) baseStart_5485784 baseEnd_5485784 := by
    simpa [prefixWord, tailWord_5485784, baseEnd_5485784] using wordTrace_append hprefix tailTrace_5485784
  have hstable : (prefixWord ++ tailWord_5485784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485784).length < 2 ^ (prefixWord ++ tailWord_5485784).sum := by decide
  have hdescent : baseEnd_5485784 < baseStart_5485784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485797 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_5485797 : Nat := 118140960795 + 5485797 * 2 ^ 59
def prefixEnd_5485797 : Nat := 4983230072969 + 3 ^ 40 * 5485797 * 2
def baseEnd_5485797 : Nat := 2816850633992778527708785

theorem tailTrace_5485797 : CollatzResearch.WordTrace tailWord_5485797 prefixEnd_5485797 2816850633992778527708785 := by
  unfold tailWord_5485797
  simp only [CollatzResearch.WordTrace]
  refine ⟨200083454106901843382327645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133388969404601228921551763 200083454106901843382327645)
  ·
    refine ⟨75031295290088191268372867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200083454106901843382327645 75031295290088191268372867)
    ·
      refine ⟨112546942935132286902559301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75031295290088191268372867 112546942935132286902559301)
      ·
        refine ⟨21102551800337303794229869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112546942935132286902559301 21102551800337303794229869)
        ·
          refine ⟨7913456925126488922836201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21102551800337303794229869 7913456925126488922836201)
          ·
            refine ⟨5935092693844866692127151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7913456925126488922836201 5935092693844866692127151)
            ·
              refine ⟨8902639040767300038190727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935092693844866692127151 8902639040767300038190727)
              ·
                refine ⟨13353958561150950057286091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8902639040767300038190727 13353958561150950057286091)
                ·
                  refine ⟨20030937841726425085929137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13353958561150950057286091 20030937841726425085929137)
                  ·
                    refine ⟨15023203381294818814446853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20030937841726425085929137 15023203381294818814446853)
                    ·
                      refine ⟨2816850633992778527708785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15023203381294818814446853 2816850633992778527708785)
                      ·
                        rfl

theorem cell23_5485797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_5485797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485797 prefixEnd_5485797 := by exact prefixLift 5485797
  have htrace : WordTrace (prefixWord ++ tailWord_5485797) baseStart_5485797 baseEnd_5485797 := by
    simpa [prefixWord, tailWord_5485797, baseEnd_5485797] using wordTrace_append hprefix tailTrace_5485797
  have hstable : (prefixWord ++ tailWord_5485797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485797).length < 2 ^ (prefixWord ++ tailWord_5485797).sum := by decide
  have hdescent : baseEnd_5485797 < baseStart_5485797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485807 : List Nat := [1, 1, 2, 1, 8, 1, 2, 7]
def baseStart_5485807 : Nat := 118140960795 + 5485807 * 2 ^ 59
def prefixEnd_5485807 : Nat := 4983230072969 + 3 ^ 40 * 5485807 * 2
def baseEnd_5485807 : Nat := 104327991437011981058657

theorem tailTrace_5485807 : CollatzResearch.WordTrace tailWord_5485807 prefixEnd_5485807 104327991437011981058657 := by
  unfold tailWord_5485807
  simp only [CollatzResearch.WordTrace]
  refine ⟨200083818836865615090191675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133389212557910410060127783 200083818836865615090191675)
  ·
    refine ⟨300125728255298422635287513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200083818836865615090191675 300125728255298422635287513)
    ·
      refine ⟨225094296191473816976465635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300125728255298422635287513 225094296191473816976465635)
      ·
        refine ⟨337641444287210725464698453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225094296191473816976465635 337641444287210725464698453)
        ·
          refine ⟨3956735675240750689039435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 337641444287210725464698453 3956735675240750689039435)
          ·
            refine ⟨5935103512861126033559153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956735675240750689039435 5935103512861126033559153)
            ·
              refine ⟨4451327634645844525169365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5935103512861126033559153 4451327634645844525169365)
              ·
                refine ⟨104327991437011981058657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4451327634645844525169365 104327991437011981058657)
                ·
                  rfl

theorem cell23_5485807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 7].length) (baseStart_5485807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485807 prefixEnd_5485807 := by exact prefixLift 5485807
  have htrace : WordTrace (prefixWord ++ tailWord_5485807) baseStart_5485807 baseEnd_5485807 := by
    simpa [prefixWord, tailWord_5485807, baseEnd_5485807] using wordTrace_append hprefix tailTrace_5485807
  have hstable : (prefixWord ++ tailWord_5485807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485807).length < 2 ^ (prefixWord ++ tailWord_5485807).sum := by decide
  have hdescent : baseEnd_5485807 < baseStart_5485807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485812 : List Nat := [2, 6, 1, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5485812 : Nat := 118140960795 + 5485812 * 2 ^ 59
def prefixEnd_5485812 : Nat := 4983230072969 + 3 ^ 40 * 5485812 * 2
def baseEnd_5485812 : Nat := 2816858336202595969021217

theorem tailTrace_5485812 : CollatzResearch.WordTrace tailWord_5485812 prefixEnd_5485812 2816858336202595969021217 := by
  unfold tailWord_5485812
  simp only [CollatzResearch.WordTrace]
  refine ⟨100042000600923750472061845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133389334134565000629415793 100042000600923750472061845)
  ·
    refine ⟨4689468778168300803377899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 100042000600923750472061845 4689468778168300803377899)
    ·
      refine ⟨7034203167252451205066849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689468778168300803377899 7034203167252451205066849)
      ·
        refine ⟨5275652375439338403800137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7034203167252451205066849 5275652375439338403800137)
        ·
          refine ⟨3956739281579503802850103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5275652375439338403800137 3956739281579503802850103)
          ·
            refine ⟨5935108922369255704275155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956739281579503802850103 5935108922369255704275155)
            ·
              refine ⟨8902663383553883556412733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935108922369255704275155 8902663383553883556412733)
              ·
                refine ⟨3338498768832706333654775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8902663383553883556412733 3338498768832706333654775)
                ·
                  refine ⟨5007748153249059500482163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3338498768832706333654775 5007748153249059500482163)
                  ·
                    refine ⟨7511622229873589250723245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5007748153249059500482163 7511622229873589250723245)
                    ·
                      refine ⟨2816858336202595969021217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7511622229873589250723245 2816858336202595969021217)
                      ·
                        rfl

theorem cell23_5485812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5485812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485812 prefixEnd_5485812 := by exact prefixLift 5485812
  have htrace : WordTrace (prefixWord ++ tailWord_5485812) baseStart_5485812 baseEnd_5485812 := by
    simpa [prefixWord, tailWord_5485812, baseEnd_5485812] using wordTrace_append hprefix tailTrace_5485812
  have hstable : (prefixWord ++ tailWord_5485812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485812).length < 2 ^ (prefixWord ++ tailWord_5485812).sum := by decide
  have hdescent : baseEnd_5485812 < baseStart_5485812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485827 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 1, 3, 2]
def baseStart_5485827 : Nat := 118140960795 + 5485827 * 2 ^ 59
def prefixEnd_5485827 : Nat := 4983230072969 + 3 ^ 40 * 5485827 * 2
def baseEnd_5485827 : Nat := 2816866038412413410333647

theorem tailTrace_5485827 : CollatzResearch.WordTrace tailWord_5485827 prefixEnd_5485827 2816866038412413410333647 := by
  unfold tailWord_5485827
  simp only [CollatzResearch.WordTrace]
  refine ⟨200084548296793158505919735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133389698864528772337279823 200084548296793158505919735)
  ·
    refine ⟨300126822445189737758879603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200084548296793158505919735 300126822445189737758879603)
    ·
      refine ⟨450190233667784606638319405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300126822445189737758879603 450190233667784606638319405)
      ·
        refine ⟨168821337625419227489369777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450190233667784606638319405 168821337625419227489369777)
        ·
          refine ⟨126616003219064420617027333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168821337625419227489369777 126616003219064420617027333)
          ·
            refine ⟨23740500603574578865692625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126616003219064420617027333 23740500603574578865692625)
            ·
              refine ⟨17805375452680934149269469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23740500603574578865692625 17805375452680934149269469)
              ·
                refine ⟨6677015794755350305976051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17805375452680934149269469 6677015794755350305976051)
                ·
                  refine ⟨10015523692133025458964077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6677015794755350305976051 10015523692133025458964077)
                  ·
                    refine ⟨3755821384549884547111529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10015523692133025458964077 3755821384549884547111529)
                    ·
                      refine ⟨2816866038412413410333647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3755821384549884547111529 2816866038412413410333647)
                      ·
                        rfl

theorem cell23_5485827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_5485827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485827 prefixEnd_5485827 := by exact prefixLift 5485827
  have htrace : WordTrace (prefixWord ++ tailWord_5485827) baseStart_5485827 baseEnd_5485827 := by
    simpa [prefixWord, tailWord_5485827, baseEnd_5485827] using wordTrace_append hprefix tailTrace_5485827
  have hstable : (prefixWord ++ tailWord_5485827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485827).length < 2 ^ (prefixWord ++ tailWord_5485827).sum := by decide
  have hdescent : baseEnd_5485827 < baseStart_5485827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485880 : List Nat := [2, 1, 2, 1, 3, 1, 1, 7, 5]
def baseStart_5485880 : Nat := 118140960795 + 5485880 * 2 ^ 59
def prefixEnd_5485880 : Nat := 4983230072969 + 3 ^ 40 * 5485880 * 2
def baseEnd_5485880 : Nat := 312988139209677966996767

theorem tailTrace_5485880 : CollatzResearch.WordTrace tailWord_5485880 prefixEnd_5485880 312988139209677966996767 := by
  unfold tailWord_5485880
  simp only [CollatzResearch.WordTrace]
  refine ⟨100043240682800574278799547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133390987577067432371732729 100043240682800574278799547)
  ·
    refine ⟨150064861024200861418199321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100043240682800574278799547 150064861024200861418199321)
    ·
      refine ⟨112548645768150646063649491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150064861024200861418199321 112548645768150646063649491)
      ·
        refine ⟨168822968652225969095474237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112548645768150646063649491 168822968652225969095474237)
        ·
          refine ⟨63308613244584738410802839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168822968652225969095474237 63308613244584738410802839)
          ·
            refine ⟨94962919866877107616204259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63308613244584738410802839 94962919866877107616204259)
            ·
              refine ⟨142444379800315661424306389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94962919866877107616204259 142444379800315661424306389)
              ·
                refine ⟨3338540151569898314632181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142444379800315661424306389 3338540151569898314632181)
                ·
                  refine ⟨312988139209677966996767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3338540151569898314632181 312988139209677966996767)
                  ·
                    rfl

theorem cell23_5485880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 5].length) (baseStart_5485880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485880 prefixEnd_5485880 := by exact prefixLift 5485880
  have htrace : WordTrace (prefixWord ++ tailWord_5485880) baseStart_5485880 baseEnd_5485880 := by
    simpa [prefixWord, tailWord_5485880, baseEnd_5485880] using wordTrace_append hprefix tailTrace_5485880
  have hstable : (prefixWord ++ tailWord_5485880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485880).length < 2 ^ (prefixWord ++ tailWord_5485880).sum := by decide
  have hdescent : baseEnd_5485880 < baseStart_5485880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485897 : List Nat := [1, 2, 1, 1, 2, 3, 6, 2, 5]
def baseStart_5485897 : Nat := 118140960795 + 5485897 * 2 ^ 59
def prefixEnd_5485897 : Nat := 4983230072969 + 3 ^ 40 * 5485897 * 2
def baseEnd_5485897 : Nat := 312989109117580904050925

theorem tailTrace_5485897 : CollatzResearch.WordTrace tailWord_5485897 prefixEnd_5485897 312989109117580904050925 := by
  unfold tailWord_5485897
  simp only [CollatzResearch.WordTrace]
  refine ⟨200087101406539560460967945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133391400937693040307311963 200087101406539560460967945)
  ·
    refine ⟨150065326054904670345725959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200087101406539560460967945 150065326054904670345725959)
    ·
      refine ⟨225097989082357005518588939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150065326054904670345725959 225097989082357005518588939)
      ·
        refine ⟨337646983623535508277883409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225097989082357005518588939 337646983623535508277883409)
        ·
          refine ⟨253235237717651631208412557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337646983623535508277883409 253235237717651631208412557)
          ·
            refine ⟨94963214144119361703154709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253235237717651631208412557 94963214144119361703154709)
            ·
              refine ⟨4451400663005595079835377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94963214144119361703154709 4451400663005595079835377)
              ·
                refine ⟨3338550497254196309876533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4451400663005595079835377 3338550497254196309876533)
                ·
                  refine ⟨312989109117580904050925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3338550497254196309876533 312989109117580904050925)
                  ·
                    rfl

theorem cell23_5485897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 5].length) (baseStart_5485897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485897 prefixEnd_5485897 := by exact prefixLift 5485897
  have htrace : WordTrace (prefixWord ++ tailWord_5485897) baseStart_5485897 baseEnd_5485897 := by
    simpa [prefixWord, tailWord_5485897, baseEnd_5485897] using wordTrace_append hprefix tailTrace_5485897
  have hstable : (prefixWord ++ tailWord_5485897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485897).length < 2 ^ (prefixWord ++ tailWord_5485897).sum := by decide
  have hdescent : baseEnd_5485897 < baseStart_5485897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5485943 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_5485943 : Nat := 118140960795 + 5485943 * 2 ^ 59
def prefixEnd_5485943 : Nat := 4983230072969 + 3 ^ 40 * 5485943 * 2
def baseEnd_5485943 : Nat := 2816925602168334956483113

theorem tailTrace_5485943 : CollatzResearch.WordTrace tailWord_5485943 prefixEnd_5485943 2816925602168334956483113 := by
  unfold tailWord_5485943
  simp only [CollatzResearch.WordTrace]
  refine ⟨200088779164372910317142483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133392519442915273544761655 200088779164372910317142483)
  ·
    refine ⟨300133168746559365475713725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200088779164372910317142483 300133168746559365475713725)
    ·
      refine ⟨112549938279959762053392647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300133168746559365475713725 112549938279959762053392647)
      ·
        refine ⟨168824907419939643080088971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112549938279959762053392647 168824907419939643080088971)
        ·
          refine ⟨253237361129909464620133457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168824907419939643080088971 253237361129909464620133457)
          ·
            refine ⟨189928020847432098465100093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253237361129909464620133457 189928020847432098465100093)
            ·
              refine ⟨71223007817787036924412535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189928020847432098465100093 71223007817787036924412535)
              ·
                refine ⟨106834511726680555386618803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71223007817787036924412535 106834511726680555386618803)
                ·
                  refine ⟨160251767590020833079928205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106834511726680555386618803 160251767590020833079928205)
                  ·
                    refine ⟨60094412846257812404973077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160251767590020833079928205 60094412846257812404973077)
                    ·
                      refine ⟨2816925602168334956483113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60094412846257812404973077 2816925602168334956483113)
                      ·
                        rfl

theorem cell23_5485943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_5485943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5485943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5485943 prefixEnd_5485943 := by exact prefixLift 5485943
  have htrace : WordTrace (prefixWord ++ tailWord_5485943) baseStart_5485943 baseEnd_5485943 := by
    simpa [prefixWord, tailWord_5485943, baseEnd_5485943] using wordTrace_append hprefix tailTrace_5485943
  have hstable : (prefixWord ++ tailWord_5485943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5485943).length < 2 ^ (prefixWord ++ tailWord_5485943).sum := by decide
  have hdescent : baseEnd_5485943 < baseStart_5485943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5485943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486037 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5486037 : Nat := 118140960795 + 5486037 * 2 ^ 59
def prefixEnd_5486037 : Nat := 4983230072969 + 3 ^ 40 * 5486037 * 2
def baseEnd_5486037 : Nat := 2816973869349857588707681

theorem tailTrace_5486037 : CollatzResearch.WordTrace tailWord_5486037 prefixEnd_5486037 2816973869349857588707681 := by
  unfold tailWord_5486037
  simp only [CollatzResearch.WordTrace]
  refine ⟨200092207626032364371064365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133394805084021576247376243 200092207626032364371064365)
  ·
    refine ⟨75034577859762136639149137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200092207626032364371064365 75034577859762136639149137)
    ·
      refine ⟨56275933394821602479361853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75034577859762136639149137 56275933394821602479361853)
      ·
        refine ⟨21103475023058100929760695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56275933394821602479361853 21103475023058100929760695)
        ·
          refine ⟨31655212534587151394641043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21103475023058100929760695 31655212534587151394641043)
          ·
            refine ⟨47482818801880727091961565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31655212534587151394641043 47482818801880727091961565)
            ·
              refine ⟨17806057050705272659485587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47482818801880727091961565 17806057050705272659485587)
              ·
                refine ⟨26709085576057908989228381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17806057050705272659485587 26709085576057908989228381)
                ·
                  refine ⟨10015907091021715870960643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26709085576057908989228381 10015907091021715870960643)
                  ·
                    refine ⟨15023860636532573806440965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10015907091021715870960643 15023860636532573806440965)
                    ·
                      refine ⟨2816973869349857588707681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15023860636532573806440965 2816973869349857588707681)
                      ·
                        rfl

theorem cell23_5486037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5486037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486037 prefixEnd_5486037 := by exact prefixLift 5486037
  have htrace : WordTrace (prefixWord ++ tailWord_5486037) baseStart_5486037 baseEnd_5486037 := by
    simpa [prefixWord, tailWord_5486037, baseEnd_5486037] using wordTrace_append hprefix tailTrace_5486037
  have hstable : (prefixWord ++ tailWord_5486037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486037).length < 2 ^ (prefixWord ++ tailWord_5486037).sum := by decide
  have hdescent : baseEnd_5486037 < baseStart_5486037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486040 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_5486040 : Nat := 118140960795 + 5486040 * 2 ^ 59
def prefixEnd_5486040 : Nat := 4983230072969 + 3 ^ 40 * 5486040 * 2
def baseEnd_5486040 : Nat := 2816975409791821076970167

theorem tailTrace_5486040 : CollatzResearch.WordTrace tailWord_5486040 prefixEnd_5486040 2816975409791821076970167 := by
  unfold tailWord_5486040
  simp only [CollatzResearch.WordTrace]
  refine ⟨100046158522510747941711787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133394878030014330588949049 100046158522510747941711787)
  ·
    refine ⟨150069237783766121912567681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100046158522510747941711787 150069237783766121912567681)
    ·
      refine ⟨112551928337824591434425761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150069237783766121912567681 112551928337824591434425761)
      ·
        refine ⟨84413946253368443575819321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112551928337824591434425761 84413946253368443575819321)
        ·
          refine ⟨63310459690026332681864491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84413946253368443575819321 63310459690026332681864491)
          ·
            refine ⟨94965689535039499022796737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63310459690026332681864491 94965689535039499022796737)
            ·
              refine ⟨71224267151279624267097553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94965689535039499022796737 71224267151279624267097553)
              ·
                refine ⟨53418200363459718200323165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71224267151279624267097553 53418200363459718200323165)
                ·
                  refine ⟨20031825136297394325121187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53418200363459718200323165 20031825136297394325121187)
                  ·
                    refine ⟨30047737704446091487681781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20031825136297394325121187 30047737704446091487681781)
                    ·
                      refine ⟨2816975409791821076970167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30047737704446091487681781 2816975409791821076970167)
                      ·
                        rfl

theorem cell23_5486040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_5486040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486040 prefixEnd_5486040 := by exact prefixLift 5486040
  have htrace : WordTrace (prefixWord ++ tailWord_5486040) baseStart_5486040 baseEnd_5486040 := by
    simpa [prefixWord, tailWord_5486040, baseEnd_5486040] using wordTrace_append hprefix tailTrace_5486040
  have hstable : (prefixWord ++ tailWord_5486040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486040).length < 2 ^ (prefixWord ++ tailWord_5486040).sum := by decide
  have hdescent : baseEnd_5486040 < baseStart_5486040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486064 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 2, 4]
def baseStart_5486064 : Nat := 118140960795 + 5486064 * 2 ^ 59
def prefixEnd_5486064 : Nat := 4983230072969 + 3 ^ 40 * 5486064 * 2
def baseEnd_5486064 : Nat := 938995911109176327690019

theorem tailTrace_5486064 : CollatzResearch.WordTrace tailWord_5486064 prefixEnd_5486064 938995911109176327690019 := by
  unfold tailWord_5486064
  simp only [CollatzResearch.WordTrace]
  refine ⟨100046596198467273991148623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133395461597956365321531497 100046596198467273991148623)
  ·
    refine ⟨150069894297700910986722935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100046596198467273991148623 150069894297700910986722935)
    ·
      refine ⟨225104841446551366480084403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150069894297700910986722935 225104841446551366480084403)
      ·
        refine ⟨337657262169827049720126605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225104841446551366480084403 337657262169827049720126605)
        ·
          refine ⟨126621473313685143645047477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337657262169827049720126605 126621473313685143645047477)
          ·
            refine ⟨11870763123157982216723201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126621473313685143645047477 11870763123157982216723201)
            ·
              refine ⟨8903072342368486662542401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11870763123157982216723201 8903072342368486662542401)
              ·
                refine ⟨6677304256776364996906801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8903072342368486662542401 6677304256776364996906801)
                ·
                  refine ⟨5007978192582273747680101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6677304256776364996906801 5007978192582273747680101)
                  ·
                    refine ⟨938995911109176327690019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5007978192582273747680101 938995911109176327690019)
                    ·
                      rfl

theorem cell23_5486064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_5486064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486064 prefixEnd_5486064 := by exact prefixLift 5486064
  have htrace : WordTrace (prefixWord ++ tailWord_5486064) baseStart_5486064 baseEnd_5486064 := by
    simpa [prefixWord, tailWord_5486064, baseEnd_5486064] using wordTrace_append hprefix tailTrace_5486064
  have hstable : (prefixWord ++ tailWord_5486064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486064).length < 2 ^ (prefixWord ++ tailWord_5486064).sum := by decide
  have hdescent : baseEnd_5486064 < baseStart_5486064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486077 : List Nat := [1, 4, 1, 1, 1, 6, 1, 8]
def baseStart_5486077 : Nat := 118140960795 + 5486077 * 2 ^ 59
def prefixEnd_5486077 : Nat := 4983230072969 + 3 ^ 40 * 5486077 * 2
def baseEnd_5486077 : Nat := 104333126243556941933611

theorem tailTrace_5486077 : CollatzResearch.WordTrace tailWord_5486077 prefixEnd_5486077 104333126243556941933611 := by
  unfold tailWord_5486077
  simp only [CollatzResearch.WordTrace]
  refine ⟨200093666545887451202520485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133395777697258300801680323 200093666545887451202520485)
  ·
    refine ⟨37517562477353897100472591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200093666545887451202520485 37517562477353897100472591)
    ·
      refine ⟨56276343716030845650708887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37517562477353897100472591 56276343716030845650708887)
      ·
        refine ⟨84414515574046268476063331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56276343716030845650708887 84414515574046268476063331)
        ·
          refine ⟨126621773361069402714094997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84414515574046268476063331 126621773361069402714094997)
          ·
            refine ⟨5935395626300128252223203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126621773361069402714094997 5935395626300128252223203)
            ·
              refine ⟨8903093439450192378334805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935395626300128252223203 8903093439450192378334805)
              ·
                refine ⟨104333126243556941933611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8903093439450192378334805 104333126243556941933611)
                ·
                  rfl

theorem cell23_5486077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 8].length) (baseStart_5486077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486077 prefixEnd_5486077 := by exact prefixLift 5486077
  have htrace : WordTrace (prefixWord ++ tailWord_5486077) baseStart_5486077 baseEnd_5486077 := by
    simpa [prefixWord, tailWord_5486077, baseEnd_5486077] using wordTrace_append hprefix tailTrace_5486077
  have hstable : (prefixWord ++ tailWord_5486077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486077).length < 2 ^ (prefixWord ++ tailWord_5486077).sum := by decide
  have hdescent : baseEnd_5486077 < baseStart_5486077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486094 : List Nat := [4, 1, 1, 2, 4, 1, 3, 7]
def baseStart_5486094 : Nat := 118140960795 + 5486094 * 2 ^ 59
def prefixEnd_5486094 : Nat := 4983230072969 + 3 ^ 40 * 5486094 * 2
def baseEnd_5486094 : Nat := 104333449546191254284997

theorem tailTrace_5486094 : CollatzResearch.WordTrace tailWord_5486094 prefixEnd_5486094 104333449546191254284997 := by
  unfold tailWord_5486094
  simp only [CollatzResearch.WordTrace]
  refine ⟨25011785823353232888236167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133396191057883908737259557 25011785823353232888236167)
  ·
    refine ⟨37517678735029849332354251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25011785823353232888236167 37517678735029849332354251)
    ·
      refine ⟨56276518102544773998531377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37517678735029849332354251 56276518102544773998531377)
      ·
        refine ⟨42207388576908580498898533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56276518102544773998531377 42207388576908580498898533)
        ·
          refine ⟨7913885358170358843543475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42207388576908580498898533 7913885358170358843543475)
          ·
            refine ⟨11870828037255538265315213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7913885358170358843543475 11870828037255538265315213)
            ·
              refine ⟨4451560513970826849493205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11870828037255538265315213 4451560513970826849493205)
              ·
                refine ⟨104333449546191254284997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4451560513970826849493205 104333449546191254284997)
                ·
                  rfl

theorem cell23_5486094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_5486094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486094 prefixEnd_5486094 := by exact prefixLift 5486094
  have htrace : WordTrace (prefixWord ++ tailWord_5486094) baseStart_5486094 baseEnd_5486094 := by
    simpa [prefixWord, tailWord_5486094, baseEnd_5486094] using wordTrace_append hprefix tailTrace_5486094
  have hstable : (prefixWord ++ tailWord_5486094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486094).length < 2 ^ (prefixWord ++ tailWord_5486094).sum := by decide
  have hdescent : baseEnd_5486094 < baseStart_5486094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486127 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 10, 2]
def baseStart_5486127 : Nat := 118140960795 + 5486127 * 2 ^ 59
def prefixEnd_5486127 : Nat := 4983230072969 + 3 ^ 40 * 5486127 * 2
def baseEnd_5486127 : Nat := 2817020082608762236582267

theorem tailTrace_5486127 : CollatzResearch.WordTrace tailWord_5486127 prefixEnd_5486127 2817020082608762236582267 := by
  unfold tailWord_5486127
  simp only [CollatzResearch.WordTrace]
  refine ⟨200095490195706309741840635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133396993463804206494560423 200095490195706309741840635)
  ·
    refine ⟨300143235293559464612760953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200095490195706309741840635 300143235293559464612760953)
    ·
      refine ⟨225107426470169598459570715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300143235293559464612760953 225107426470169598459570715)
      ·
        refine ⟨337661139705254397689356073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225107426470169598459570715 337661139705254397689356073)
        ·
          refine ⟨253245854778940798267017055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337661139705254397689356073 253245854778940798267017055)
          ·
            refine ⟨379868782168411197400525583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253245854778940798267017055 379868782168411197400525583)
            ·
              refine ⟨569803173252616796100788375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379868782168411197400525583 569803173252616796100788375)
              ·
                refine ⟨854704759878925194151182563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569803173252616796100788375 854704759878925194151182563)
                ·
                  refine ⟨1282057139818387791226773845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854704759878925194151182563 1282057139818387791226773845)
                  ·
                    refine ⟨3756026776811682982109689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1282057139818387791226773845 3756026776811682982109689)
                    ·
                      refine ⟨2817020082608762236582267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756026776811682982109689 2817020082608762236582267)
                      ·
                        rfl

theorem cell23_5486127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 10, 2].length) (baseStart_5486127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486127 prefixEnd_5486127 := by exact prefixLift 5486127
  have htrace : WordTrace (prefixWord ++ tailWord_5486127) baseStart_5486127 baseEnd_5486127 := by
    simpa [prefixWord, tailWord_5486127, baseEnd_5486127] using wordTrace_append hprefix tailTrace_5486127
  have hstable : (prefixWord ++ tailWord_5486127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486127).length < 2 ^ (prefixWord ++ tailWord_5486127).sum := by decide
  have hdescent : baseEnd_5486127 < baseStart_5486127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486137 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 2, 6]
def baseStart_5486137 : Nat := 118140960795 + 5486137 * 2 ^ 59
def prefixEnd_5486137 : Nat := 4983230072969 + 3 ^ 40 * 5486137 * 2
def baseEnd_5486137 : Nat := 939008405805102399152407

theorem tailTrace_5486137 : CollatzResearch.WordTrace tailWord_5486137 prefixEnd_5486137 939008405805102399152407 := by
  unfold tailWord_5486137
  simp only [CollatzResearch.WordTrace]
  refine ⟨200095854925670081449704665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133397236617113387633136443 200095854925670081449704665)
  ·
    refine ⟨150071891194252561087278499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200095854925670081449704665 150071891194252561087278499)
    ·
      refine ⟨225107836791378841630917749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150071891194252561087278499 225107836791378841630917749)
      ·
        refine ⟨21103859699191766402898539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 225107836791378841630917749 21103859699191766402898539)
        ·
          refine ⟨31655789548787649604347809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21103859699191766402898539 31655789548787649604347809)
          ·
            refine ⟨23741842161590737203260857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31655789548787649604347809 23741842161590737203260857)
            ·
              refine ⟨17806381621193052902445643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23741842161590737203260857 17806381621193052902445643)
              ·
                refine ⟨26709572431789579353668465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17806381621193052902445643 26709572431789579353668465)
                ·
                  refine ⟨20032179323842184515251349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26709572431789579353668465 20032179323842184515251349)
                  ·
                    refine ⟨939008405805102399152407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20032179323842184515251349 939008405805102399152407)
                    ·
                      rfl

theorem cell23_5486137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_5486137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486137 prefixEnd_5486137 := by exact prefixLift 5486137
  have htrace : WordTrace (prefixWord ++ tailWord_5486137) baseStart_5486137 baseEnd_5486137 := by
    simpa [prefixWord, tailWord_5486137, baseEnd_5486137] using wordTrace_append hprefix tailTrace_5486137
  have hstable : (prefixWord ++ tailWord_5486137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486137).length < 2 ^ (prefixWord ++ tailWord_5486137).sum := by decide
  have hdescent : baseEnd_5486137 < baseStart_5486137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486184 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 7]
def baseStart_5486184 : Nat := 118140960795 + 5486184 * 2 ^ 59
def prefixEnd_5486184 : Nat := 4983230072969 + 3 ^ 40 * 5486184 * 2
def baseEnd_5486184 : Nat := 313005483445118723729945

theorem tailTrace_5486184 : CollatzResearch.WordTrace tailWord_5486184 prefixEnd_5486184 313005483445118723729945 := by
  unfold tailWord_5486184
  simp only [CollatzResearch.WordTrace]
  refine ⟨100048784578249904238332803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133398379437666538984443737 100048784578249904238332803)
  ·
    refine ⟨150073176867374856357499205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100048784578249904238332803 150073176867374856357499205)
    ·
      refine ⟨28138720662632785567031101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150073176867374856357499205 28138720662632785567031101)
      ·
        refine ⟨10552020248487294587636663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28138720662632785567031101 10552020248487294587636663)
        ·
          refine ⟨15828030372730941881454995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10552020248487294587636663 15828030372730941881454995)
          ·
            refine ⟨23742045559096412822182493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15828030372730941881454995 23742045559096412822182493)
            ·
              refine ⟨8903267084661154808318435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23742045559096412822182493 8903267084661154808318435)
              ·
                refine ⟨13354900626991732212477653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8903267084661154808318435 13354900626991732212477653)
                ·
                  refine ⟨313005483445118723729945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13354900626991732212477653 313005483445118723729945)
                  ·
                    rfl

theorem cell23_5486184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 7].length) (baseStart_5486184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486184 prefixEnd_5486184 := by exact prefixLift 5486184
  have htrace : WordTrace (prefixWord ++ tailWord_5486184) baseStart_5486184 baseEnd_5486184 := by
    simpa [prefixWord, tailWord_5486184, baseEnd_5486184] using wordTrace_append hprefix tailTrace_5486184
  have hstable : (prefixWord ++ tailWord_5486184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486184).length < 2 ^ (prefixWord ++ tailWord_5486184).sum := by decide
  have hdescent : baseEnd_5486184 < baseStart_5486184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486217 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 4]
def baseStart_5486217 : Nat := 118140960795 + 5486217 * 2 ^ 59
def prefixEnd_5486217 : Nat := 4983230072969 + 3 ^ 40 * 5486217 * 2
def baseEnd_5486217 : Nat := 2817066295867666884456853

theorem tailTrace_5486217 : CollatzResearch.WordTrace tailWord_5486217 prefixEnd_5486217 2817066295867666884456853 := by
  unfold tailWord_5486217
  simp only [CollatzResearch.WordTrace]
  refine ⟨200098772765380255112616905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133399181843586836741744603 200098772765380255112616905)
  ·
    refine ⟨150074079574035191334462679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200098772765380255112616905 150074079574035191334462679)
    ·
      refine ⟨225111119361052787001694019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150074079574035191334462679 225111119361052787001694019)
      ·
        refine ⟨337666679041579180502541029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225111119361052787001694019 337666679041579180502541029)
        ·
          refine ⟨63312502320296096344226443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 337666679041579180502541029 63312502320296096344226443)
          ·
            refine ⟨94968753480444144516339665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63312502320296096344226443 94968753480444144516339665)
            ·
              refine ⟨71226565110333108387254749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94968753480444144516339665 71226565110333108387254749)
              ·
                refine ⟨26709961916374915645220531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71226565110333108387254749 26709961916374915645220531)
                ·
                  refine ⟨40064942874562373467830797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26709961916374915645220531 40064942874562373467830797)
                  ·
                    refine ⟨15024353577960890050436549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40064942874562373467830797 15024353577960890050436549)
                    ·
                      refine ⟨2817066295867666884456853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15024353577960890050436549 2817066295867666884456853)
                      ·
                        rfl

theorem cell23_5486217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 4].length) (baseStart_5486217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486217 prefixEnd_5486217 := by exact prefixLift 5486217
  have htrace : WordTrace (prefixWord ++ tailWord_5486217) baseStart_5486217 baseEnd_5486217 := by
    simpa [prefixWord, tailWord_5486217, baseEnd_5486217] using wordTrace_append hprefix tailTrace_5486217
  have hstable : (prefixWord ++ tailWord_5486217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486217).length < 2 ^ (prefixWord ++ tailWord_5486217).sum := by decide
  have hdescent : baseEnd_5486217 < baseStart_5486217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486237 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5486237 : Nat := 118140960795 + 5486237 * 2 ^ 59
def prefixEnd_5486237 : Nat := 4983230072969 + 3 ^ 40 * 5486237 * 2
def baseEnd_5486237 : Nat := 2817076565480756806206761

theorem tailTrace_5486237 : CollatzResearch.WordTrace tailWord_5486237 prefixEnd_5486237 2817076565480756806206761 := by
  unfold tailWord_5486237
  simp only [CollatzResearch.WordTrace]
  refine ⟨200099502225307798528344965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133399668150205199018896643 200099502225307798528344965)
  ·
    refine ⟨37518656667245212224064681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200099502225307798528344965 37518656667245212224064681)
    ·
      refine ⟨28138992500433909168048511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37518656667245212224064681 28138992500433909168048511)
      ·
        refine ⟨42208488750650863752072767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28138992500433909168048511 42208488750650863752072767)
        ·
          refine ⟨63312733125976295628109151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42208488750650863752072767 63312733125976295628109151)
          ·
            refine ⟨94969099688964443442163727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63312733125976295628109151 94969099688964443442163727)
            ·
              refine ⟨142453649533446665163245591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94969099688964443442163727 142453649533446665163245591)
              ·
                refine ⟨213680474300169997744868387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142453649533446665163245591 213680474300169997744868387)
                ·
                  refine ⟨320520711450254996617302581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213680474300169997744868387 320520711450254996617302581)
                  ·
                    refine ⟨30048816698461405932872117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 320520711450254996617302581 30048816698461405932872117)
                    ·
                      refine ⟨2817076565480756806206761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30048816698461405932872117 2817076565480756806206761)
                      ·
                        rfl

theorem cell23_5486237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5486237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486237 prefixEnd_5486237 := by exact prefixLift 5486237
  have htrace : WordTrace (prefixWord ++ tailWord_5486237) baseStart_5486237 baseEnd_5486237 := by
    simpa [prefixWord, tailWord_5486237, baseEnd_5486237] using wordTrace_append hprefix tailTrace_5486237
  have hstable : (prefixWord ++ tailWord_5486237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486237).length < 2 ^ (prefixWord ++ tailWord_5486237).sum := by decide
  have hdescent : baseEnd_5486237 < baseStart_5486237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486321 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 1, 5]
def baseStart_5486321 : Nat := 118140960795 + 5486321 * 2 ^ 59
def prefixEnd_5486321 : Nat := 4983230072969 + 3 ^ 40 * 5486321 * 2
def baseEnd_5486321 : Nat := 939039899285244825852125

theorem tailTrace_5486321 : CollatzResearch.WordTrace tailWord_5486321 prefixEnd_5486321 939039899285244825852125 := by
  unfold tailWord_5486321
  simp only [CollatzResearch.WordTrace]
  refine ⟨200102565957003480874402817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133401710638002320582935211 200102565957003480874402817)
  ·
    refine ⟨150076924467752610655802113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200102565957003480874402817 150076924467752610655802113)
    ·
      refine ⟨112557693350814457991851585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150076924467752610655802113 112557693350814457991851585)
      ·
        refine ⟨84418270013110843493888689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112557693350814457991851585 84418270013110843493888689)
        ·
          refine ⟨63313702509833132620416517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84418270013110843493888689 63313702509833132620416517)
          ·
            refine ⟨11871319220593712366328097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63313702509833132620416517 11871319220593712366328097)
            ·
              refine ⟨8903489415445284274746073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11871319220593712366328097 8903489415445284274746073)
              ·
                refine ⟨6677617061583963206059555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8903489415445284274746073 6677617061583963206059555)
                ·
                  refine ⟨10016425592375944809089333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6677617061583963206059555 10016425592375944809089333)
                  ·
                    refine ⟨939039899285244825852125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10016425592375944809089333 939039899285244825852125)
                    ·
                      rfl

theorem cell23_5486321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_5486321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486321 prefixEnd_5486321 := by exact prefixLift 5486321
  have htrace : WordTrace (prefixWord ++ tailWord_5486321) baseStart_5486321 baseEnd_5486321 := by
    simpa [prefixWord, tailWord_5486321, baseEnd_5486321] using wordTrace_append hprefix tailTrace_5486321
  have hstable : (prefixWord ++ tailWord_5486321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486321).length < 2 ^ (prefixWord ++ tailWord_5486321).sum := by decide
  have hdescent : baseEnd_5486321 < baseStart_5486321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486347 : List Nat := [1, 1, 1, 1, 5, 1, 13]
def baseStart_5486347 : Nat := 118140960795 + 5486347 * 2 ^ 59
def prefixEnd_5486347 : Nat := 4983230072969 + 3 ^ 40 * 5486347 * 2
def baseEnd_5486347 : Nat := 34779420350033967602855

theorem tailTrace_5486347 : CollatzResearch.WordTrace tailWord_5486347 prefixEnd_5486347 34779420350033967602855 := by
  unfold tailWord_5486347
  simp only [CollatzResearch.WordTrace]
  refine ⟨200103514254909287314849295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133402342836606191543232863 200103514254909287314849295)
  ·
    refine ⟨300155271382363930972273943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200103514254909287314849295 300155271382363930972273943)
    ·
      refine ⟨450232907073545896458410915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300155271382363930972273943 450232907073545896458410915)
      ·
        refine ⟨675349360610318844687616373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450232907073545896458410915 675349360610318844687616373)
        ·
          refine ⟨63314002557217391689464035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 675349360610318844687616373 63314002557217391689464035)
          ·
            refine ⟨94971003835826087534196053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63314002557217391689464035 94971003835826087534196053)
            ·
              refine ⟨34779420350033967602855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 94971003835826087534196053 34779420350033967602855)
              ·
                rfl

theorem cell23_5486347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 13].length) (baseStart_5486347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486347 prefixEnd_5486347 := by exact prefixLift 5486347
  have htrace : WordTrace (prefixWord ++ tailWord_5486347) baseStart_5486347 baseEnd_5486347 := by
    simpa [prefixWord, tailWord_5486347, baseEnd_5486347] using wordTrace_append hprefix tailTrace_5486347
  have hstable : (prefixWord ++ tailWord_5486347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486347).length < 2 ^ (prefixWord ++ tailWord_5486347).sum := by decide
  have hdescent : baseEnd_5486347 < baseStart_5486347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486364 : List Nat := [2, 2, 3, 1, 1, 2, 4, 8]
def baseStart_5486364 : Nat := 118140960795 + 5486364 * 2 ^ 59
def prefixEnd_5486364 : Nat := 4983230072969 + 3 ^ 40 * 5486364 * 2
def baseEnd_5486364 : Nat := 104338584352736215159951

theorem tailTrace_5486364 : CollatzResearch.WordTrace tailWord_5486364 prefixEnd_5486364 104338584352736215159951 := by
  unfold tailWord_5486364
  simp only [CollatzResearch.WordTrace]
  refine ⟨100052067147923849609109073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133402756197231799478812097 100052067147923849609109073)
  ·
    refine ⟨75039050360942887206831805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100052067147923849609109073 75039050360942887206831805)
    ·
      refine ⟨28139643885353582702561927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75039050360942887206831805 28139643885353582702561927)
      ·
        refine ⟨42209465828030374053842891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28139643885353582702561927 42209465828030374053842891)
        ·
          refine ⟨63314198742045561080764337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42209465828030374053842891 63314198742045561080764337)
          ·
            refine ⟨47485649056534170810573253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63314198742045561080764337 47485649056534170810573253)
            ·
              refine ⟨8903559198100157026982485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47485649056534170810573253 8903559198100157026982485)
              ·
                refine ⟨104338584352736215159951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8903559198100157026982485 104338584352736215159951)
                ·
                  rfl

theorem cell23_5486364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 8].length) (baseStart_5486364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486364 prefixEnd_5486364 := by exact prefixLift 5486364
  have htrace : WordTrace (prefixWord ++ tailWord_5486364) baseStart_5486364 baseEnd_5486364 := by
    simpa [prefixWord, tailWord_5486364, baseEnd_5486364] using wordTrace_append hprefix tailTrace_5486364
  have hstable : (prefixWord ++ tailWord_5486364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486364).length < 2 ^ (prefixWord ++ tailWord_5486364).sum := by decide
  have hdescent : baseEnd_5486364 < baseStart_5486364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486388 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5486388 : Nat := 118140960795 + 5486388 * 2 ^ 59
def prefixEnd_5486388 : Nat := 4983230072969 + 3 ^ 40 * 5486388 * 2
def baseEnd_5486388 : Nat := 2817154101059585715418567

theorem tailTrace_5486388 : CollatzResearch.WordTrace tailWord_5486388 prefixEnd_5486388 2817154101059585715418567 := by
  unfold tailWord_5486388
  simp only [CollatzResearch.WordTrace]
  refine ⟨100052504823880375658545909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133403339765173834211394545 100052504823880375658545909)
  ·
    refine ⟨9379922327238785217988679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100052504823880375658545909 9379922327238785217988679)
    ·
      refine ⟨14069883490858177826983019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9379922327238785217988679 14069883490858177826983019)
      ·
        refine ⟨21104825236287266740474529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14069883490858177826983019 21104825236287266740474529)
        ·
          refine ⟨15828618927215450055355897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21104825236287266740474529 15828618927215450055355897)
          ·
            refine ⟨11871464195411587541516923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15828618927215450055355897 11871464195411587541516923)
            ·
              refine ⟨17807196293117381312275385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871464195411587541516923 17807196293117381312275385)
              ·
                refine ⟨13355397219838035984206539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17807196293117381312275385 13355397219838035984206539)
                ·
                  refine ⟨20033095829757053976309809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13355397219838035984206539 20033095829757053976309809)
                  ·
                    refine ⟨15024821872317790482232357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20033095829757053976309809 15024821872317790482232357)
                    ·
                      refine ⟨2817154101059585715418567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15024821872317790482232357 2817154101059585715418567)
                      ·
                        rfl

theorem cell23_5486388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5486388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486388 prefixEnd_5486388 := by exact prefixLift 5486388
  have htrace : WordTrace (prefixWord ++ tailWord_5486388) baseStart_5486388 baseEnd_5486388 := by
    simpa [prefixWord, tailWord_5486388, baseEnd_5486388] using wordTrace_append hprefix tailTrace_5486388
  have hstable : (prefixWord ++ tailWord_5486388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486388).length < 2 ^ (prefixWord ++ tailWord_5486388).sum := by decide
  have hdescent : baseEnd_5486388 < baseStart_5486388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486391 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_5486391 : Nat := 118140960795 + 5486391 * 2 ^ 59
def prefixEnd_5486391 : Nat := 4983230072969 + 3 ^ 40 * 5486391 * 2
def baseEnd_5486391 : Nat := 2817155641501549203681053

theorem tailTrace_5486391 : CollatzResearch.WordTrace tailWord_5486391 prefixEnd_5486391 2817155641501549203681053 := by
  unfold tailWord_5486391
  simp only [CollatzResearch.WordTrace]
  refine ⟨200105119066749882829451027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133403412711166588552967351 200105119066749882829451027)
  ·
    refine ⟨300157678600124824244176541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200105119066749882829451027 300157678600124824244176541)
    ·
      refine ⟨112559129475046809091566203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300157678600124824244176541 112559129475046809091566203)
      ·
        refine ⟨168838694212570213637349305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112559129475046809091566203 168838694212570213637349305)
        ·
          refine ⟨126629020659427660228011979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168838694212570213637349305 126629020659427660228011979)
          ·
            refine ⟨189943530989141490342017969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126629020659427660228011979 189943530989141490342017969)
            ·
              refine ⟨142457648241856117756513477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189943530989141490342017969 142457648241856117756513477)
              ·
                refine ⟨26710809045348022079346277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142457648241856117756513477 26710809045348022079346277)
                ·
                  refine ⟨5008276696002754139877427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26710809045348022079346277 5008276696002754139877427)
                  ·
                    refine ⟨7512415044004131209816141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008276696002754139877427 7512415044004131209816141)
                    ·
                      refine ⟨2817155641501549203681053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7512415044004131209816141 2817155641501549203681053)
                      ·
                        rfl

theorem cell23_5486391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_5486391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486391 prefixEnd_5486391 := by exact prefixLift 5486391
  have htrace : WordTrace (prefixWord ++ tailWord_5486391) baseStart_5486391 baseEnd_5486391 := by
    simpa [prefixWord, tailWord_5486391, baseEnd_5486391] using wordTrace_append hprefix tailTrace_5486391
  have hstable : (prefixWord ++ tailWord_5486391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486391).length < 2 ^ (prefixWord ++ tailWord_5486391).sum := by decide
  have hdescent : baseEnd_5486391 < baseStart_5486391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486408 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_5486408 : Nat := 118140960795 + 5486408 * 2 ^ 59
def prefixEnd_5486408 : Nat := 4983230072969 + 3 ^ 40 * 5486408 * 2
def baseEnd_5486408 : Nat := 2817164370672675637168475

theorem tailTrace_5486408 : CollatzResearch.WordTrace tailWord_5486408 prefixEnd_5486408 2817164370672675637168475 := by
  unfold tailWord_5486408
  simp only [CollatzResearch.WordTrace]
  refine ⟨100052869553844147366409939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133403826071792196488546585 100052869553844147366409939)
  ·
    refine ⟨150079304330766221049614909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100052869553844147366409939 150079304330766221049614909)
    ·
      refine ⟨56279739124037332893605591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150079304330766221049614909 56279739124037332893605591)
      ·
        refine ⟨84419608686055999340408387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56279739124037332893605591 84419608686055999340408387)
        ·
          refine ⟨126629413029083999010612581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84419608686055999340408387 126629413029083999010612581)
          ·
            refine ⟨23743014942953249814489859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126629413029083999010612581 23743014942953249814489859)
            ·
              refine ⟨35614522414429874721734789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23743014942953249814489859 35614522414429874721734789)
              ·
                refine ⟨6677722952705601510325273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35614522414429874721734789 6677722952705601510325273)
                ·
                  refine ⟨5008292214529201132743955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6677722952705601510325273 5008292214529201132743955)
                  ·
                    refine ⟨7512438321793801699115933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008292214529201132743955 7512438321793801699115933)
                    ·
                      refine ⟨2817164370672675637168475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7512438321793801699115933 2817164370672675637168475)
                      ·
                        rfl

theorem cell23_5486408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_5486408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486408 prefixEnd_5486408 := by exact prefixLift 5486408
  have htrace : WordTrace (prefixWord ++ tailWord_5486408) baseStart_5486408 baseEnd_5486408 := by
    simpa [prefixWord, tailWord_5486408, baseEnd_5486408] using wordTrace_append hprefix tailTrace_5486408
  have hstable : (prefixWord ++ tailWord_5486408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486408).length < 2 ^ (prefixWord ++ tailWord_5486408).sum := by decide
  have hdescent : baseEnd_5486408 < baseStart_5486408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486418 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_5486418 : Nat := 118140960795 + 5486418 * 2 ^ 59
def prefixEnd_5486418 : Nat := 4983230072969 + 3 ^ 40 * 5486418 * 2
def baseEnd_5486418 : Nat := 2817169505479220598043429

theorem tailTrace_5486418 : CollatzResearch.WordTrace tailWord_5486418 prefixEnd_5486418 2817169505479220598043429 := by
  unfold tailWord_5486418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50026525959413016610170977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133404069225101377627122605 50026525959413016610170977)
  ·
    refine ⟨37519894469559762457628233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50026525959413016610170977 37519894469559762457628233)
    ·
      refine ⟨28139920852169821843221175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37519894469559762457628233 28139920852169821843221175)
      ·
        refine ⟨42209881278254732764831763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28139920852169821843221175 42209881278254732764831763)
        ·
          refine ⟨63314821917382099147247645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42209881278254732764831763 63314821917382099147247645)
          ·
            refine ⟨23743058219018287180217867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63314821917382099147247645 23743058219018287180217867)
            ·
              refine ⟨35614587328527430770326801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23743058219018287180217867 35614587328527430770326801)
              ·
                refine ⟨26710940496395573077745101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35614587328527430770326801 26710940496395573077745101)
                ·
                  refine ⟨10016602686148339904154413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26710940496395573077745101 10016602686148339904154413)
                  ·
                    refine ⟨3756226007305627464057905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10016602686148339904154413 3756226007305627464057905)
                    ·
                      refine ⟨2817169505479220598043429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756226007305627464057905 2817169505479220598043429)
                      ·
                        rfl

theorem cell23_5486418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_5486418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486418 prefixEnd_5486418 := by exact prefixLift 5486418
  have htrace : WordTrace (prefixWord ++ tailWord_5486418) baseStart_5486418 baseEnd_5486418 := by
    simpa [prefixWord, tailWord_5486418, baseEnd_5486418] using wordTrace_append hprefix tailTrace_5486418
  have hstable : (prefixWord ++ tailWord_5486418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486418).length < 2 ^ (prefixWord ++ tailWord_5486418).sum := by decide
  have hdescent : baseEnd_5486418 < baseStart_5486418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486448 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 4, 2, 2]
def baseStart_5486448 : Nat := 118140960795 + 5486448 * 2 ^ 59
def prefixEnd_5486448 : Nat := 4983230072969 + 3 ^ 40 * 5486448 * 2
def baseEnd_5486448 : Nat := 2817184909898855480668291

theorem tailTrace_5486448 : CollatzResearch.WordTrace tailWord_5486448 prefixEnd_5486448 2817184909898855480668291 := by
  unfold tailWord_5486448
  simp only [CollatzResearch.WordTrace]
  refine ⟨100053599013771690782137999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133404798685028921042850665 100053599013771690782137999)
  ·
    refine ⟨150080398520657536173206999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100053599013771690782137999 150080398520657536173206999)
    ·
      refine ⟨225120597780986304259810499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150080398520657536173206999 225120597780986304259810499)
      ·
        refine ⟨337680896671479456389715749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225120597780986304259810499 337680896671479456389715749)
        ·
          refine ⟨63315168125902398073071703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 337680896671479456389715749 63315168125902398073071703)
          ·
            refine ⟨94972752188853597109607555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63315168125902398073071703 94972752188853597109607555)
            ·
              refine ⟨142459128283280395664411333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94972752188853597109607555 142459128283280395664411333)
              ·
                refine ⟨26711086553115074187077125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142459128283280395664411333 26711086553115074187077125)
                ·
                  refine ⟨5008328728709076410076961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26711086553115074187077125 5008328728709076410076961)
                  ·
                    refine ⟨3756246546531807307557721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5008328728709076410076961 3756246546531807307557721)
                    ·
                      refine ⟨2817184909898855480668291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756246546531807307557721 2817184909898855480668291)
                      ·
                        rfl

theorem cell23_5486448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 2, 2].length) (baseStart_5486448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486448 prefixEnd_5486448 := by exact prefixLift 5486448
  have htrace : WordTrace (prefixWord ++ tailWord_5486448) baseStart_5486448 baseEnd_5486448 := by
    simpa [prefixWord, tailWord_5486448, baseEnd_5486448] using wordTrace_append hprefix tailTrace_5486448
  have hstable : (prefixWord ++ tailWord_5486448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486448).length < 2 ^ (prefixWord ++ tailWord_5486448).sum := by decide
  have hdescent : baseEnd_5486448 < baseStart_5486448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486481 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 3]
def baseStart_5486481 : Nat := 118140960795 + 5486481 * 2 ^ 59
def prefixEnd_5486481 : Nat := 4983230072969 + 3 ^ 40 * 5486481 * 2
def baseEnd_5486481 : Nat := 2817201854760453851555639

theorem tailTrace_5486481 : CollatzResearch.WordTrace tailWord_5486481 prefixEnd_5486481 2817201854760453851555639 := by
  unfold tailWord_5486481
  simp only [CollatzResearch.WordTrace]
  refine ⟨200108401636423828200227297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133405601090949218800151531 200108401636423828200227297)
  ·
    refine ⟨150081301227317871150170473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200108401636423828200227297 150081301227317871150170473)
    ·
      refine ⟨112560975920488403362627855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150081301227317871150170473 112560975920488403362627855)
      ·
        refine ⟨168841463880732605043941783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112560975920488403362627855 168841463880732605043941783)
        ·
          refine ⟨253262195821098907565912675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168841463880732605043941783 253262195821098907565912675)
          ·
            refine ⟨379893293731648361348869013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253262195821098907565912675 379893293731648361348869013)
            ·
              refine ⟨17807498143671016938228235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 379893293731648361348869013 17807498143671016938228235)
              ·
                refine ⟨26711247215506525407342353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17807498143671016938228235 26711247215506525407342353)
                ·
                  refine ⟨20033435411629894055506765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26711247215506525407342353 20033435411629894055506765)
                  ·
                    refine ⟨7512538279361210270815037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20033435411629894055506765 7512538279361210270815037)
                    ·
                      refine ⟨2817201854760453851555639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7512538279361210270815037 2817201854760453851555639)
                      ·
                        rfl

theorem cell23_5486481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_5486481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486481 prefixEnd_5486481 := by exact prefixLift 5486481
  have htrace : WordTrace (prefixWord ++ tailWord_5486481) baseStart_5486481 baseEnd_5486481 := by
    simpa [prefixWord, tailWord_5486481, baseEnd_5486481] using wordTrace_append hprefix tailTrace_5486481
  have hstable : (prefixWord ++ tailWord_5486481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486481).length < 2 ^ (prefixWord ++ tailWord_5486481).sum := by decide
  have hdescent : baseEnd_5486481 < baseStart_5486481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486482 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5486482 : Nat := 118140960795 + 5486482 * 2 ^ 59
def prefixEnd_5486482 : Nat := 4983230072969 + 3 ^ 40 * 5486482 * 2
def baseEnd_5486482 : Nat := 2817202368241108347643135

theorem tailTrace_5486482 : CollatzResearch.WordTrace tailWord_5486482 prefixEnd_5486482 2817202368241108347643135 := by
  unfold tailWord_5486482
  simp only [CollatzResearch.WordTrace]
  refine ⟨50027109527355051342753425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133405625406280136914009133 50027109527355051342753425)
  ·
    refine ⟨37520332145516288507065069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50027109527355051342753425 37520332145516288507065069)
    ·
      refine ⟨14070124554568608190149401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37520332145516288507065069 14070124554568608190149401)
      ·
        refine ⟨10552593415926456142612051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14070124554568608190149401 10552593415926456142612051)
        ·
          refine ⟨15828890123889684213918077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10552593415926456142612051 15828890123889684213918077)
          ·
            refine ⟨5935833796458631580219279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15828890123889684213918077 5935833796458631580219279)
            ·
              refine ⟨8903750694687947370328919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5935833796458631580219279 8903750694687947370328919)
              ·
                refine ⟨13355626042031921055493379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8903750694687947370328919 13355626042031921055493379)
                ·
                  refine ⟨20033439063047881583240069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13355626042031921055493379 20033439063047881583240069)
                  ·
                    refine ⟨3756269824321477796857513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20033439063047881583240069 3756269824321477796857513)
                    ·
                      refine ⟨2817202368241108347643135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756269824321477796857513 2817202368241108347643135)
                      ·
                        rfl

theorem cell23_5486482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5486482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486482 prefixEnd_5486482 := by exact prefixLift 5486482
  have htrace : WordTrace (prefixWord ++ tailWord_5486482) baseStart_5486482 baseEnd_5486482 := by
    simpa [prefixWord, tailWord_5486482, baseEnd_5486482] using wordTrace_append hprefix tailTrace_5486482
  have hstable : (prefixWord ++ tailWord_5486482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486482).length < 2 ^ (prefixWord ++ tailWord_5486482).sum := by decide
  have hdescent : baseEnd_5486482 < baseStart_5486482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486486 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5486486 : Nat := 118140960795 + 5486486 * 2 ^ 59
def prefixEnd_5486486 : Nat := 4983230072969 + 3 ^ 40 * 5486486 * 2
def baseEnd_5486486 : Nat := 2817204422163726331993117

theorem tailTrace_5486486 : CollatzResearch.WordTrace tailWord_5486486 prefixEnd_5486486 2817204422163726331993117 := by
  unfold tailWord_5486486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506786500087857128384957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133405722667603809369439541 12506786500087857128384957)
  ·
    refine ⟨4690044937532946423144359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12506786500087857128384957 4690044937532946423144359)
    ·
      refine ⟨7035067406299419634716539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690044937532946423144359 7035067406299419634716539)
      ·
        refine ⟨10552601109449129452074809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035067406299419634716539 10552601109449129452074809)
        ·
          refine ⟨7914450832086847089056107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10552601109449129452074809 7914450832086847089056107)
          ·
            refine ⟨11871676248130270633584161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914450832086847089056107 11871676248130270633584161)
            ·
              refine ⟨8903757186097702975188121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11871676248130270633584161 8903757186097702975188121)
              ·
                refine ⟨6677817889573277231391091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8903757186097702975188121 6677817889573277231391091)
                ·
                  refine ⟨10016726834359915847086637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6677817889573277231391091 10016726834359915847086637)
                  ·
                    refine ⟨3756272562884968442657489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10016726834359915847086637 3756272562884968442657489)
                    ·
                      refine ⟨2817204422163726331993117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756272562884968442657489 2817204422163726331993117)
                      ·
                        rfl

theorem cell23_5486486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5486486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486486 prefixEnd_5486486 := by exact prefixLift 5486486
  have htrace : WordTrace (prefixWord ++ tailWord_5486486) baseStart_5486486 baseEnd_5486486 := by
    simpa [prefixWord, tailWord_5486486, baseEnd_5486486] using wordTrace_append hprefix tailTrace_5486486
  have hstable : (prefixWord ++ tailWord_5486486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486486).length < 2 ^ (prefixWord ++ tailWord_5486486).sum := by decide
  have hdescent : baseEnd_5486486 < baseStart_5486486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486538 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_5486538 : Nat := 118140960795 + 5486538 * 2 ^ 59
def prefixEnd_5486538 : Nat := 4983230072969 + 3 ^ 40 * 5486538 * 2
def baseEnd_5486538 : Nat := 2817231123157760128542877

theorem tailTrace_5486538 : CollatzResearch.WordTrace tailWord_5486538 prefixEnd_5486538 2817231123157760128542877 := by
  unfold tailWord_5486538
  simp only [CollatzResearch.WordTrace]
  refine ⟨50027620149304331733763067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133406987064811551290034845 50027620149304331733763067)
  ·
    refine ⟨75041430223956497600644601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50027620149304331733763067 75041430223956497600644601)
    ·
      refine ⟨56281072667967373200483451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75041430223956497600644601 56281072667967373200483451)
      ·
        refine ⟨84421609001951059800725177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56281072667967373200483451 84421609001951059800725177)
        ·
          refine ⟨63316206751463294850543883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84421609001951059800725177 63316206751463294850543883)
          ·
            refine ⟨94974310127194942275815825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63316206751463294850543883 94974310127194942275815825)
            ·
              refine ⟨71230732595396206706861869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94974310127194942275815825 71230732595396206706861869)
              ·
                refine ⟨26711524723273577515073201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71230732595396206706861869 26711524723273577515073201)
                ·
                  refine ⟨20033643542455183136304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26711524723273577515073201 20033643542455183136304901)
                  ·
                    refine ⟨3756308164210346838057169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20033643542455183136304901 3756308164210346838057169)
                    ·
                      refine ⟨2817231123157760128542877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756308164210346838057169 2817231123157760128542877)
                      ·
                        rfl

theorem cell23_5486538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_5486538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486538 prefixEnd_5486538 := by exact prefixLift 5486538
  have htrace : WordTrace (prefixWord ++ tailWord_5486538) baseStart_5486538 baseEnd_5486538 := by
    simpa [prefixWord, tailWord_5486538, baseEnd_5486538] using wordTrace_append hprefix tailTrace_5486538
  have hstable : (prefixWord ++ tailWord_5486538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486538).length < 2 ^ (prefixWord ++ tailWord_5486538).sum := by decide
  have hdescent : baseEnd_5486538 < baseStart_5486538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486548 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_5486548 : Nat := 118140960795 + 5486548 * 2 ^ 59
def prefixEnd_5486548 : Nat := 4983230072969 + 3 ^ 40 * 5486548 * 2
def baseEnd_5486548 : Nat := 939078752654768363139277

theorem tailTrace_5486548 : CollatzResearch.WordTrace tailWord_5486548 prefixEnd_5486548 939078752654768363139277 := by
  unfold tailWord_5486548
  simp only [CollatzResearch.WordTrace]
  refine ⟨100055422663590549321458149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133407230218120732428610865 100055422663590549321458149)
  ·
    refine ⟨18760391749423227997773403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100055422663590549321458149 18760391749423227997773403)
    ·
      refine ⟨28140587624134841996660105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18760391749423227997773403 28140587624134841996660105)
      ·
        refine ⟨21105440718101131497495079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28140587624134841996660105 21105440718101131497495079)
        ·
          refine ⟨31658161077151697246242619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21105440718101131497495079 31658161077151697246242619)
          ·
            refine ⟨47487241615727545869363929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31658161077151697246242619 47487241615727545869363929)
            ·
              refine ⟨35615431211795659402022947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47487241615727545869363929 35615431211795659402022947)
              ·
                refine ⟨53423146817693489103034421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35615431211795659402022947 53423146817693489103034421)
                ·
                  refine ⟨5008420014158764603409477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53423146817693489103034421 5008420014158764603409477)
                  ·
                    refine ⟨939078752654768363139277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5008420014158764603409477 939078752654768363139277)
                    ·
                      rfl

theorem cell23_5486548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_5486548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486548 prefixEnd_5486548 := by exact prefixLift 5486548
  have htrace : WordTrace (prefixWord ++ tailWord_5486548) baseStart_5486548 baseEnd_5486548 := by
    simpa [prefixWord, tailWord_5486548, baseEnd_5486548] using wordTrace_append hprefix tailTrace_5486548
  have hstable : (prefixWord ++ tailWord_5486548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486548).length < 2 ^ (prefixWord ++ tailWord_5486548).sum := by decide
  have hdescent : baseEnd_5486548 < baseStart_5486548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486625 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 1, 5]
def baseStart_5486625 : Nat := 118140960795 + 5486625 * 2 ^ 59
def prefixEnd_5486625 : Nat := 4983230072969 + 3 ^ 40 * 5486625 * 2
def baseEnd_5486625 : Nat := 939091931991567096051659

theorem tailTrace_5486625 : CollatzResearch.WordTrace tailWord_5486625 prefixEnd_5486625 939091931991567096051659 := by
  unfold tailWord_5486625
  simp only [CollatzResearch.WordTrace]
  refine ⟨200113653747902140793469329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133409102498601427195646219 200113653747902140793469329)
  ·
    refine ⟨150085240310926605595101997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200113653747902140793469329 150085240310926605595101997)
    ·
      refine ⟨56281965116597477098163249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150085240310926605595101997 56281965116597477098163249)
      ·
        refine ⟨42211473837448107823622437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56281965116597477098163249 42211473837448107823622437)
        ·
          refine ⟨7914651344521520216929207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42211473837448107823622437 7914651344521520216929207)
          ·
            refine ⟨11871977016782280325393811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914651344521520216929207 11871977016782280325393811)
            ·
              refine ⟨17807965525173420488090717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871977016782280325393811 17807965525173420488090717)
              ·
                refine ⟨6677987071940032683034019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17807965525173420488090717 6677987071940032683034019)
                ·
                  refine ⟨10016980607910049024551029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6677987071940032683034019 10016980607910049024551029)
                  ·
                    refine ⟨939091931991567096051659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10016980607910049024551029 939091931991567096051659)
                    ·
                      rfl

theorem cell23_5486625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_5486625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486625 prefixEnd_5486625 := by exact prefixLift 5486625
  have htrace : WordTrace (prefixWord ++ tailWord_5486625) baseStart_5486625 baseEnd_5486625 := by
    simpa [prefixWord, tailWord_5486625, baseEnd_5486625] using wordTrace_append hprefix tailTrace_5486625
  have hstable : (prefixWord ++ tailWord_5486625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486625).length < 2 ^ (prefixWord ++ tailWord_5486625).sum := by decide
  have hdescent : baseEnd_5486625 < baseStart_5486625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486662 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5486662 : Nat := 118140960795 + 5486662 * 2 ^ 59
def prefixEnd_5486662 : Nat := 4983230072969 + 3 ^ 40 * 5486662 * 2
def baseEnd_5486662 : Nat := 2817294794758917643392307

theorem tailTrace_5486662 : CollatzResearch.WordTrace tailWord_5486662 prefixEnd_5486662 2817294794758917643392307 := by
  unfold tailWord_5486662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253593851524003003517695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133410002165845397408377493 6253593851524003003517695)
  ·
    refine ⟨9380390777286004505276543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6253593851524003003517695 9380390777286004505276543)
    ·
      refine ⟨14070586165929006757914815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9380390777286004505276543 14070586165929006757914815)
      ·
        refine ⟨21105879248893510136872223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14070586165929006757914815 21105879248893510136872223)
        ·
          refine ⟨31658818873340265205308335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21105879248893510136872223 31658818873340265205308335)
          ·
            refine ⟨47488228310010397807962503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31658818873340265205308335 47488228310010397807962503)
            ·
              refine ⟨71232342465015596711943755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47488228310010397807962503 71232342465015596711943755)
              ·
                refine ⟨106848513697523395067915633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71232342465015596711943755 106848513697523395067915633)
                ·
                  refine ⟨80136385273142546300936725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106848513697523395067915633 80136385273142546300936725)
                  ·
                    refine ⟨3756393059678556857856409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80136385273142546300936725 3756393059678556857856409)
                    ·
                      refine ⟨2817294794758917643392307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756393059678556857856409 2817294794758917643392307)
                      ·
                        rfl

theorem cell23_5486662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5486662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486662 prefixEnd_5486662 := by exact prefixLift 5486662
  have htrace : WordTrace (prefixWord ++ tailWord_5486662) baseStart_5486662 baseEnd_5486662 := by
    simpa [prefixWord, tailWord_5486662, baseEnd_5486662] using wordTrace_append hprefix tailTrace_5486662
  have hstable : (prefixWord ++ tailWord_5486662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486662).length < 2 ^ (prefixWord ++ tailWord_5486662).sum := by decide
  have hdescent : baseEnd_5486662 < baseStart_5486662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486665 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 3]
def baseStart_5486665 : Nat := 118140960795 + 5486665 * 2 ^ 59
def prefixEnd_5486665 : Nat := 4983230072969 + 3 ^ 40 * 5486665 * 2
def baseEnd_5486665 : Nat := 2817296335200881131654793

theorem tailTrace_5486665 : CollatzResearch.WordTrace tailWord_5486665 prefixEnd_5486665 2817296335200881131654793 := by
  unfold tailWord_5486665
  simp only [CollatzResearch.WordTrace]
  refine ⟨200115112667757227624925449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133410075111838151749950299 200115112667757227624925449)
  ·
    refine ⟨150086334500817920718694087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200115112667757227624925449 150086334500817920718694087)
    ·
      refine ⟨225129501751226881078041131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150086334500817920718694087 225129501751226881078041131)
      ·
        refine ⟨337694252626840321617061697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225129501751226881078041131 337694252626840321617061697)
        ·
          refine ⟨253270689470130241212796273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337694252626840321617061697 253270689470130241212796273)
          ·
            refine ⟨189953017102597680909597205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253270689470130241212796273 189953017102597680909597205)
            ·
              refine ⟨8904047676684266292637369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189953017102597680909597205 8904047676684266292637369)
              ·
                refine ⟨6678035757513199719478027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8904047676684266292637369 6678035757513199719478027)
                ·
                  refine ⟨10017053636269799579217041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6678035757513199719478027 10017053636269799579217041)
                  ·
                    refine ⟨7512790227202349684412781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10017053636269799579217041 7512790227202349684412781)
                    ·
                      refine ⟨2817296335200881131654793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7512790227202349684412781 2817296335200881131654793)
                      ·
                        rfl

theorem cell23_5486665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 3].length) (baseStart_5486665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486665 prefixEnd_5486665 := by exact prefixLift 5486665
  have htrace : WordTrace (prefixWord ++ tailWord_5486665) baseStart_5486665 baseEnd_5486665 := by
    simpa [prefixWord, tailWord_5486665, baseEnd_5486665] using wordTrace_append hprefix tailTrace_5486665
  have hstable : (prefixWord ++ tailWord_5486665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486665).length < 2 ^ (prefixWord ++ tailWord_5486665).sum := by decide
  have hdescent : baseEnd_5486665 < baseStart_5486665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486668 : List Nat := [2, 2, 1, 3, 1, 1, 6, 7]
def baseStart_5486668 : Nat := 118140960795 + 5486668 * 2 ^ 59
def prefixEnd_5486668 : Nat := 4983230072969 + 3 ^ 40 * 5486668 * 2
def baseEnd_5486668 : Nat := 104344365764549800737677

theorem tailTrace_5486668 : CollatzResearch.WordTrace tailWord_5486668 prefixEnd_5486668 104344365764549800737677 := by
  unfold tailWord_5486668
  simp only [CollatzResearch.WordTrace]
  refine ⟨100057611043373179568642329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133410148057830906091523105 100057611043373179568642329)
  ·
    refine ⟨75043208282529884676481747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100057611043373179568642329 75043208282529884676481747)
    ·
      refine ⟨112564812423794827014722621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75043208282529884676481747 112564812423794827014722621)
      ·
        refine ⟨42211804658923060130520983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112564812423794827014722621 42211804658923060130520983)
        ·
          refine ⟨63317706988384590195781475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42211804658923060130520983 63317706988384590195781475)
          ·
            refine ⟨94976560482576885293672213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63317706988384590195781475 94976560482576885293672213)
            ·
              refine ⟨4452026272620791498140885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94976560482576885293672213 4452026272620791498140885)
              ·
                refine ⟨104344365764549800737677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4452026272620791498140885 104344365764549800737677)
                ·
                  rfl

theorem cell23_5486668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 7].length) (baseStart_5486668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486668 prefixEnd_5486668 := by exact prefixLift 5486668
  have htrace : WordTrace (prefixWord ++ tailWord_5486668) baseStart_5486668 baseEnd_5486668 := by
    simpa [prefixWord, tailWord_5486668, baseEnd_5486668] using wordTrace_append hprefix tailTrace_5486668
  have hstable : (prefixWord ++ tailWord_5486668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486668).length < 2 ^ (prefixWord ++ tailWord_5486668).sum := by decide
  have hdescent : baseEnd_5486668 < baseStart_5486668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486679 : List Nat := [1, 1, 3, 2, 2, 1, 5, 3, 1, 2, 2]
def baseStart_5486679 : Nat := 118140960795 + 5486679 * 2 ^ 59
def prefixEnd_5486679 : Nat := 4983230072969 + 3 ^ 40 * 5486679 * 2
def baseEnd_5486679 : Nat := 2817303523930044076879729

theorem tailTrace_5486679 : CollatzResearch.WordTrace tailWord_5486679 prefixEnd_5486679 2817303523930044076879729 := by
  unfold tailWord_5486679
  simp only [CollatzResearch.WordTrace]
  refine ⟨200115623289706508015935091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133410415526471005343956727 200115623289706508015935091)
  ·
    refine ⟨300173434934559762023902637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200115623289706508015935091 300173434934559762023902637)
    ·
      refine ⟨112565038100459910758963489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300173434934559762023902637 112565038100459910758963489)
      ·
        refine ⟨84423778575344933069222617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112565038100459910758963489 84423778575344933069222617)
        ·
          refine ⟨63317833931508699801916963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84423778575344933069222617 63317833931508699801916963)
          ·
            refine ⟨94976750897263049702875445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63317833931508699801916963 94976750897263049702875445)
            ·
              refine ⟨8904070396618410909644573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94976750897263049702875445 8904070396618410909644573)
              ·
                refine ⟨3339026398731904091116715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8904070396618410909644573 3339026398731904091116715)
                ·
                  refine ⟨5008539598097856136675073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339026398731904091116715 5008539598097856136675073)
                  ·
                    refine ⟨3756404698573392102506305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5008539598097856136675073 3756404698573392102506305)
                    ·
                      refine ⟨2817303523930044076879729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756404698573392102506305 2817303523930044076879729)
                      ·
                        rfl

theorem cell23_5486679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_5486679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486679 prefixEnd_5486679 := by exact prefixLift 5486679
  have htrace : WordTrace (prefixWord ++ tailWord_5486679) baseStart_5486679 baseEnd_5486679 := by
    simpa [prefixWord, tailWord_5486679, baseEnd_5486679] using wordTrace_append hprefix tailTrace_5486679
  have hstable : (prefixWord ++ tailWord_5486679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486679).length < 2 ^ (prefixWord ++ tailWord_5486679).sum := by decide
  have hdescent : baseEnd_5486679 < baseStart_5486679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486685 : List Nat := [1, 4, 4, 1, 1, 3, 9]
def baseStart_5486685 : Nat := 118140960795 + 5486685 * 2 ^ 59
def prefixEnd_5486685 : Nat := 4983230072969 + 3 ^ 40 * 5486685 * 2
def baseEnd_5486685 : Nat := 34781563022394704363021

theorem tailTrace_5486685 : CollatzResearch.WordTrace tailWord_5486685 prefixEnd_5486685 34781563022394704363021 := by
  unfold tailWord_5486685
  simp only [CollatzResearch.WordTrace]
  refine ⟨200115842127684771040653509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133410561418456514027102339 200115842127684771040653509)
  ·
    refine ⟨37521720398940894570122533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200115842127684771040653509 37521720398940894570122533)
    ·
      refine ⟨7035322574801417731897975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37521720398940894570122533 7035322574801417731897975)
      ·
        refine ⟨10552983862202126597846963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035322574801417731897975 10552983862202126597846963)
        ·
          refine ⟨15829475793303189896770445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10552983862202126597846963 15829475793303189896770445)
          ·
            refine ⟨5936053422488696211288917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15829475793303189896770445 5936053422488696211288917)
            ·
              refine ⟨34781563022394704363021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5936053422488696211288917 34781563022394704363021)
              ·
                rfl

theorem cell23_5486685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 9].length) (baseStart_5486685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486685 prefixEnd_5486685 := by exact prefixLift 5486685
  have htrace : WordTrace (prefixWord ++ tailWord_5486685) baseStart_5486685 baseEnd_5486685 := by
    simpa [prefixWord, tailWord_5486685, baseEnd_5486685] using wordTrace_append hprefix tailTrace_5486685
  have hstable : (prefixWord ++ tailWord_5486685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486685).length < 2 ^ (prefixWord ++ tailWord_5486685).sum := by decide
  have hdescent : baseEnd_5486685 < baseStart_5486685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486695 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_5486695 : Nat := 118140960795 + 5486695 * 2 ^ 59
def prefixEnd_5486695 : Nat := 4983230072969 + 3 ^ 40 * 5486695 * 2
def baseEnd_5486695 : Nat := 2817311739620516014279655

theorem tailTrace_5486695 : CollatzResearch.WordTrace tailWord_5486695 prefixEnd_5486695 2817311739620516014279655 := by
  unfold tailWord_5486695
  simp only [CollatzResearch.WordTrace]
  refine ⟨200116206857648542748517539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133410804571765695165678359 200116206857648542748517539)
  ·
    refine ⟨300174310286472814122776309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200116206857648542748517539 300174310286472814122776309)
    ·
      refine ⟨28141341589356826324010279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 300174310286472814122776309 28141341589356826324010279)
      ·
        refine ⟨42212012384035239486015419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28141341589356826324010279 42212012384035239486015419)
        ·
          refine ⟨63318018576052859229023129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42212012384035239486015419 63318018576052859229023129)
          ·
            refine ⟨47488513932039644421767347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63318018576052859229023129 47488513932039644421767347)
            ·
              refine ⟨71232770898059466632651021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47488513932039644421767347 71232770898059466632651021)
              ·
                refine ⟨26712289086772299987244133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71232770898059466632651021 26712289086772299987244133)
                ·
                  refine ⟨5008554203769806247608275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26712289086772299987244133 5008554203769806247608275)
                  ·
                    refine ⟨7512831305654709371412413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008554203769806247608275 7512831305654709371412413)
                    ·
                      refine ⟨2817311739620516014279655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7512831305654709371412413 2817311739620516014279655)
                      ·
                        rfl

theorem cell23_5486695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_5486695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486695 prefixEnd_5486695 := by exact prefixLift 5486695
  have htrace : WordTrace (prefixWord ++ tailWord_5486695) baseStart_5486695 baseEnd_5486695 := by
    simpa [prefixWord, tailWord_5486695, baseEnd_5486695] using wordTrace_append hprefix tailTrace_5486695
  have hstable : (prefixWord ++ tailWord_5486695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486695).length < 2 ^ (prefixWord ++ tailWord_5486695).sum := by decide
  have hdescent : baseEnd_5486695 < baseStart_5486695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486705 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 3, 3, 2]
def baseStart_5486705 : Nat := 118140960795 + 5486705 * 2 ^ 59
def prefixEnd_5486705 : Nat := 4983230072969 + 3 ^ 40 * 5486705 * 2
def baseEnd_5486705 : Nat := 2817316874427060975154609

theorem tailTrace_5486705 : CollatzResearch.WordTrace tailWord_5486705 prefixEnd_5486705 2817316874427060975154609 := by
  unfold tailWord_5486705
  simp only [CollatzResearch.WordTrace]
  refine ⟨200116571587612314456381569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133411047725074876304254379 200116571587612314456381569)
  ·
    refine ⟨150087428690709235842286177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200116571587612314456381569 150087428690709235842286177)
    ·
      refine ⟨112565571518031926881714633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150087428690709235842286177 112565571518031926881714633)
      ·
        refine ⟨84424178638523945161285975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112565571518031926881714633 84424178638523945161285975)
        ·
          refine ⟨126636267957785917741928963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84424178638523945161285975 126636267957785917741928963)
          ·
            refine ⟨189954401936678876612893445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126636267957785917741928963 189954401936678876612893445)
            ·
              refine ⟨35616450363127289364917521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189954401936678876612893445 35616450363127289364917521)
              ·
                refine ⟨26712337772345467023688141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35616450363127289364917521 26712337772345467023688141)
                ·
                  refine ⟨10017126664629550133883053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26712337772345467023688141 10017126664629550133883053)
                  ·
                    refine ⟨3756422499236081300206145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10017126664629550133883053 3756422499236081300206145)
                    ·
                      refine ⟨2817316874427060975154609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756422499236081300206145 2817316874427060975154609)
                      ·
                        rfl

theorem cell23_5486705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_5486705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486705 prefixEnd_5486705 := by exact prefixLift 5486705
  have htrace : WordTrace (prefixWord ++ tailWord_5486705) baseStart_5486705 baseEnd_5486705 := by
    simpa [prefixWord, tailWord_5486705, baseEnd_5486705] using wordTrace_append hprefix tailTrace_5486705
  have hstable : (prefixWord ++ tailWord_5486705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486705).length < 2 ^ (prefixWord ++ tailWord_5486705).sum := by decide
  have hdescent : baseEnd_5486705 < baseStart_5486705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486762 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5486762 : Nat := 118140960795 + 5486762 * 2 ^ 59
def prefixEnd_5486762 : Nat := 4983230072969 + 3 ^ 40 * 5486762 * 2
def baseEnd_5486762 : Nat := 939115380941455750713949

theorem tailTrace_5486762 : CollatzResearch.WordTrace tailWord_5486762 prefixEnd_5486762 939115380941455750713949 := by
  unfold tailWord_5486762
  simp only [CollatzResearch.WordTrace]
  refine ⟨50029662637101453297801635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133412433698937208794137693 50029662637101453297801635)
  ·
    refine ⟨75044493955652179946702453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50029662637101453297801635 75044493955652179946702453)
    ·
      refine ⟨7035421308342391870003355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75044493955652179946702453 7035421308342391870003355)
      ·
        refine ⟨10553131962513587805005033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035421308342391870003355 10553131962513587805005033)
        ·
          refine ⟨7914848971885190853753775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10553131962513587805005033 7914848971885190853753775)
          ·
            refine ⟨11872273457827786280630663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914848971885190853753775 11872273457827786280630663)
            ·
              refine ⟨17808410186741679420945995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11872273457827786280630663 17808410186741679420945995)
              ·
                refine ⟨26712615280112519131418993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17808410186741679420945995 26712615280112519131418993)
                ·
                  refine ⟨20034461460084389348564245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26712615280112519131418993 20034461460084389348564245)
                  ·
                    refine ⟨939115380941455750713949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20034461460084389348564245 939115380941455750713949)
                    ·
                      rfl

theorem cell23_5486762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5486762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486762 prefixEnd_5486762 := by exact prefixLift 5486762
  have htrace : WordTrace (prefixWord ++ tailWord_5486762) baseStart_5486762 baseEnd_5486762 := by
    simpa [prefixWord, tailWord_5486762, baseEnd_5486762] using wordTrace_append hprefix tailTrace_5486762
  have hstable : (prefixWord ++ tailWord_5486762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486762).length < 2 ^ (prefixWord ++ tailWord_5486762).sum := by decide
  have hdescent : baseEnd_5486762 < baseStart_5486762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486765 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_5486765 : Nat := 118140960795 + 5486765 * 2 ^ 59
def prefixEnd_5486765 : Nat := 4983230072969 + 3 ^ 40 * 5486765 * 2
def baseEnd_5486765 : Nat := 2817347683266330740404333

theorem tailTrace_5486765 : CollatzResearch.WordTrace tailWord_5486765 prefixEnd_5486765 2817347683266330740404333 := by
  unfold tailWord_5486765
  simp only [CollatzResearch.WordTrace]
  refine ⟨200118759967394944703565749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133412506644929963135710499 200118759967394944703565749)
  ·
    refine ⟨18761133746943276065959289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200118759967394944703565749 18761133746943276065959289)
    ·
      refine ⟨14070850310207457049469467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18761133746943276065959289 14070850310207457049469467)
      ·
        refine ⟨21106275465311185574204201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14070850310207457049469467 21106275465311185574204201)
        ·
          refine ⟨15829706598983389180653151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21106275465311185574204201 15829706598983389180653151)
          ·
            refine ⟨23744559898475083770979727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15829706598983389180653151 23744559898475083770979727)
            ·
              refine ⟨35616839847712625656469591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23744559898475083770979727 35616839847712625656469591)
              ·
                refine ⟨53425259771568938484704387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35616839847712625656469591 53425259771568938484704387)
                ·
                  refine ⟨80137889657353407727056581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53425259771568938484704387 80137889657353407727056581)
                  ·
                    refine ⟨15025854310753763948823109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80137889657353407727056581 15025854310753763948823109)
                    ·
                      refine ⟨2817347683266330740404333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15025854310753763948823109 2817347683266330740404333)
                      ·
                        rfl

theorem cell23_5486765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_5486765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486765 prefixEnd_5486765 := by exact prefixLift 5486765
  have htrace : WordTrace (prefixWord ++ tailWord_5486765) baseStart_5486765 baseEnd_5486765 := by
    simpa [prefixWord, tailWord_5486765, baseEnd_5486765] using wordTrace_append hprefix tailTrace_5486765
  have hstable : (prefixWord ++ tailWord_5486765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486765).length < 2 ^ (prefixWord ++ tailWord_5486765).sum := by decide
  have hdescent : baseEnd_5486765 < baseStart_5486765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486769 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 1, 4, 2]
def baseStart_5486769 : Nat := 118140960795 + 5486769 * 2 ^ 59
def prefixEnd_5486769 : Nat := 4983230072969 + 3 ^ 40 * 5486769 * 2
def baseEnd_5486769 : Nat := 2817349737188948724754315

theorem tailTrace_5486769 : CollatzResearch.WordTrace tailWord_5486769 prefixEnd_5486769 2817349737188948724754315 := by
  unfold tailWord_5486769
  simp only [CollatzResearch.WordTrace]
  refine ⟨200118905859380453386711361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133412603906253635591140907 200118905859380453386711361)
  ·
    refine ⟨150089179394535340040033521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200118905859380453386711361 150089179394535340040033521)
    ·
      refine ⟨112566884545901505030025141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 150089179394535340040033521 112566884545901505030025141)
      ·
        refine ⟨10553145426178266096564857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112566884545901505030025141 10553145426178266096564857)
        ·
          refine ⟨7914859069633699572423643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10553145426178266096564857 7914859069633699572423643)
          ·
            refine ⟨11872288604450549358635465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914859069633699572423643 11872288604450549358635465)
            ·
              refine ⟨8904216453337912018976599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11872288604450549358635465 8904216453337912018976599)
              ·
                refine ⟨13356324680006868028464899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8904216453337912018976599 13356324680006868028464899)
                ·
                  refine ⟨20034487020010302042697349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13356324680006868028464899 20034487020010302042697349)
                  ·
                    refine ⟨3756466316251931633005753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20034487020010302042697349 3756466316251931633005753)
                    ·
                      refine ⟨2817349737188948724754315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756466316251931633005753 2817349737188948724754315)
                      ·
                        rfl

theorem cell23_5486769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_5486769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486769 prefixEnd_5486769 := by exact prefixLift 5486769
  have htrace : WordTrace (prefixWord ++ tailWord_5486769) baseStart_5486769 baseEnd_5486769 := by
    simpa [prefixWord, tailWord_5486769, baseEnd_5486769] using wordTrace_append hprefix tailTrace_5486769
  have hstable : (prefixWord ++ tailWord_5486769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486769).length < 2 ^ (prefixWord ++ tailWord_5486769).sum := by decide
  have hdescent : baseEnd_5486769 < baseStart_5486769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486786 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_5486786 : Nat := 118140960795 + 5486786 * 2 ^ 59
def prefixEnd_5486786 : Nat := 4983230072969 + 3 ^ 40 * 5486786 * 2
def baseEnd_5486786 : Nat := 2817358466360075158241737

theorem tailTrace_5486786 : CollatzResearch.WordTrace tailWord_5486786 prefixEnd_5486786 2817358466360075158241737 := by
  unfold tailWord_5486786
  simp only [CollatzResearch.WordTrace]
  refine ⟨50029881475079716322520053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133413017266879243526720141 50029881475079716322520053)
  ·
    refine ⟨4690301388288723405236255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50029881475079716322520053 4690301388288723405236255)
    ·
      refine ⟨7035452082433085107854383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690301388288723405236255 7035452082433085107854383)
      ·
        refine ⟨10553178123649627661781575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035452082433085107854383 10553178123649627661781575)
        ·
          refine ⟨15829767185474441492672363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10553178123649627661781575 15829767185474441492672363)
          ·
            refine ⟨23744650778211662239008545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15829767185474441492672363 23744650778211662239008545)
            ·
              refine ⟨17808488083658746679256409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23744650778211662239008545 17808488083658746679256409)
              ·
                refine ⟨13356366062744060009442307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17808488083658746679256409 13356366062744060009442307)
                ·
                  refine ⟨20034549094116090014163461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13356366062744060009442307 20034549094116090014163461)
                  ·
                    refine ⟨3756477955146766877655649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20034549094116090014163461 3756477955146766877655649)
                    ·
                      refine ⟨2817358466360075158241737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756477955146766877655649 2817358466360075158241737)
                      ·
                        rfl

theorem cell23_5486786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_5486786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486786 prefixEnd_5486786 := by exact prefixLift 5486786
  have htrace : WordTrace (prefixWord ++ tailWord_5486786) baseStart_5486786 baseEnd_5486786 := by
    simpa [prefixWord, tailWord_5486786, baseEnd_5486786] using wordTrace_append hprefix tailTrace_5486786
  have hstable : (prefixWord ++ tailWord_5486786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486786).length < 2 ^ (prefixWord ++ tailWord_5486786).sum := by decide
  have hdescent : baseEnd_5486786 < baseStart_5486786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486835 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 3, 4]
def baseStart_5486835 : Nat := 118140960795 + 5486835 * 2 ^ 59
def prefixEnd_5486835 : Nat := 4983230072969 + 3 ^ 40 * 5486835 * 2
def baseEnd_5486835 : Nat := 939127875637381822176337

theorem tailTrace_5486835 : CollatzResearch.WordTrace tailWord_5486835 prefixEnd_5486835 939127875637381822176337 := by
  unfold tailWord_5486835
  simp only [CollatzResearch.WordTrace]
  refine ⟨200121313077141346658613959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133414208718094231105742639 200121313077141346658613959)
  ·
    refine ⟨300181969615712019987920939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200121313077141346658613959 300181969615712019987920939)
    ·
      refine ⟨450272954423568029981881409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300181969615712019987920939 450272954423568029981881409)
      ·
        refine ⟨337704715817676022486411057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450272954423568029981881409 337704715817676022486411057)
        ·
          refine ⟨253278536863257016864808293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337704715817676022486411057 253278536863257016864808293)
          ·
            refine ⟨47489725661860690662151555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 253278536863257016864808293 47489725661860690662151555)
            ·
              refine ⟨71234588492791035993227333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47489725661860690662151555 71234588492791035993227333)
              ·
                refine ⟨13356485342398319248730125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71234588492791035993227333 13356485342398319248730125)
                ·
                  refine ⟨5008682003399369718273797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13356485342398319248730125 5008682003399369718273797)
                  ·
                    refine ⟨939127875637381822176337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5008682003399369718273797 939127875637381822176337)
                    ·
                      rfl

theorem cell23_5486835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 4].length) (baseStart_5486835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486835 prefixEnd_5486835 := by exact prefixLift 5486835
  have htrace : WordTrace (prefixWord ++ tailWord_5486835) baseStart_5486835 baseEnd_5486835 := by
    simpa [prefixWord, tailWord_5486835, baseEnd_5486835] using wordTrace_append hprefix tailTrace_5486835
  have hstable : (prefixWord ++ tailWord_5486835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486835).length < 2 ^ (prefixWord ++ tailWord_5486835).sum := by decide
  have hdescent : baseEnd_5486835 < baseStart_5486835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486845 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_5486845 : Nat := 118140960795 + 5486845 * 2 ^ 59
def prefixEnd_5486845 : Nat := 4983230072969 + 3 ^ 40 * 5486845 * 2
def baseEnd_5486845 : Nat := 2817388761718690427403965

theorem tailTrace_5486845 : CollatzResearch.WordTrace tailWord_5486845 prefixEnd_5486845 2817388761718690427403965 := by
  unfold tailWord_5486845
  simp only [CollatzResearch.WordTrace]
  refine ⟨200121677807105118366477989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133414451871403412244318659 200121677807105118366477989)
  ·
    refine ⟨37522814588832209693714623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 200121677807105118366477989 37522814588832209693714623)
    ·
      refine ⟨56284221883248314540571935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37522814588832209693714623 56284221883248314540571935)
      ·
        refine ⟨84426332824872471810857903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56284221883248314540571935 84426332824872471810857903)
        ·
          refine ⟨126639499237308707716286855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84426332824872471810857903 126639499237308707716286855)
          ·
            refine ⟨189959248855963061574430283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126639499237308707716286855 189959248855963061574430283)
            ·
              refine ⟨284938873283944592361645425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189959248855963061574430283 284938873283944592361645425)
              ·
                refine ⟨213704154962958444271234069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284938873283944592361645425 213704154962958444271234069)
                ·
                  refine ⟨10017382263888677075214097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 213704154962958444271234069 10017382263888677075214097)
                  ·
                    refine ⟨7513036697916507806410573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10017382263888677075214097 7513036697916507806410573)
                    ·
                      refine ⟨2817388761718690427403965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513036697916507806410573 2817388761718690427403965)
                      ·
                        rfl

theorem cell23_5486845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_5486845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486845 prefixEnd_5486845 := by exact prefixLift 5486845
  have htrace : WordTrace (prefixWord ++ tailWord_5486845) baseStart_5486845 baseEnd_5486845 := by
    simpa [prefixWord, tailWord_5486845, baseEnd_5486845] using wordTrace_append hprefix tailTrace_5486845
  have hstable : (prefixWord ++ tailWord_5486845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486845).length < 2 ^ (prefixWord ++ tailWord_5486845).sum := by decide
  have hdescent : baseEnd_5486845 < baseStart_5486845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486848 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 8]
def baseStart_5486848 : Nat := 118140960795 + 5486848 * 2 ^ 59
def prefixEnd_5486848 : Nat := 4983230072969 + 3 ^ 40 * 5486848 * 2
def baseEnd_5486848 : Nat := 313043366906739323962939

theorem tailTrace_5486848 : CollatzResearch.WordTrace tailWord_5486848 prefixEnd_5486848 313043366906739323962939 := by
  unfold tailWord_5486848
  simp only [CollatzResearch.WordTrace]
  refine ⟨100060893613047124939418599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133414524817396166585891465 100060893613047124939418599)
  ·
    refine ⟨150091340419570687409127899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100060893613047124939418599 150091340419570687409127899)
    ·
      refine ⟨225137010629356031113691849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150091340419570687409127899 225137010629356031113691849)
      ·
        refine ⟨168852757972017023335268887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225137010629356031113691849 168852757972017023335268887)
        ·
          refine ⟨253279136958025535002903331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168852757972017023335268887 253279136958025535002903331)
          ·
            refine ⟨379918705437038302504354997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253279136958025535002903331 379918705437038302504354997)
            ·
              refine ⟨35617378634722340859783281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 379918705437038302504354997 35617378634722340859783281)
              ·
                refine ⟨26713033976041755644837461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35617378634722340859783281 26713033976041755644837461)
                ·
                  refine ⟨313043366906739323962939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26713033976041755644837461 313043366906739323962939)
                  ·
                    rfl

theorem cell23_5486848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_5486848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486848 prefixEnd_5486848 := by exact prefixLift 5486848
  have htrace : WordTrace (prefixWord ++ tailWord_5486848) baseStart_5486848 baseEnd_5486848 := by
    simpa [prefixWord, tailWord_5486848, baseEnd_5486848] using wordTrace_append hprefix tailTrace_5486848
  have hstable : (prefixWord ++ tailWord_5486848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486848).length < 2 ^ (prefixWord ++ tailWord_5486848).sum := by decide
  have hdescent : baseEnd_5486848 < baseStart_5486848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486862 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3]
def baseStart_5486862 : Nat := 118140960795 + 5486862 * 2 ^ 59
def prefixEnd_5486862 : Nat := 4983230072969 + 3 ^ 40 * 5486862 * 2
def baseEnd_5486862 : Nat := 2817397490889816860891387

theorem tailTrace_5486862 : CollatzResearch.WordTrace tailWord_5486862 prefixEnd_5486862 2817397490889816860891387 := by
  unfold tailWord_5486862
  simp only [CollatzResearch.WordTrace]
  refine ⟨25015287231005441283730855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133414865232029020179897893 25015287231005441283730855)
  ·
    refine ⟨37522930846508161925596283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25015287231005441283730855 37522930846508161925596283)
    ·
      refine ⟨56284396269762242888394425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37522930846508161925596283 56284396269762242888394425)
      ·
        refine ⟨42213297202321682166295819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56284396269762242888394425 42213297202321682166295819)
        ·
          refine ⟨63319945803482523249443729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42213297202321682166295819 63319945803482523249443729)
          ·
            refine ⟨47489959352611892437082797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63319945803482523249443729 47489959352611892437082797)
            ·
              refine ⟨17808734757229459663906049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47489959352611892437082797 17808734757229459663906049)
              ·
                refine ⟨13356551067922094747929537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17808734757229459663906049 13356551067922094747929537)
                ·
                  refine ⟨10017413300941571060947153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13356551067922094747929537 10017413300941571060947153)
                  ·
                    refine ⟨7513059975706178295710365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10017413300941571060947153 7513059975706178295710365)
                    ·
                      refine ⟨2817397490889816860891387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513059975706178295710365 2817397490889816860891387)
                      ·
                        rfl

theorem cell23_5486862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_5486862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486862 prefixEnd_5486862 := by exact prefixLift 5486862
  have htrace : WordTrace (prefixWord ++ tailWord_5486862) baseStart_5486862 baseEnd_5486862 := by
    simpa [prefixWord, tailWord_5486862, baseEnd_5486862] using wordTrace_append hprefix tailTrace_5486862
  have hstable : (prefixWord ++ tailWord_5486862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486862).length < 2 ^ (prefixWord ++ tailWord_5486862).sum := by decide
  have hdescent : baseEnd_5486862 < baseStart_5486862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486882 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 6]
def baseStart_5486882 : Nat := 118140960795 + 5486882 * 2 ^ 59
def prefixEnd_5486882 : Nat := 4983230072969 + 3 ^ 40 * 5486882 * 2
def baseEnd_5486882 : Nat := 313045306722545198071255

theorem tailTrace_5486882 : CollatzResearch.WordTrace tailWord_5486882 prefixEnd_5486882 313045306722545198071255 := by
  unfold tailWord_5486882
  simp only [CollatzResearch.WordTrace]
  refine ⟨50030756826992768421393725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133415351538647382457049933 50030756826992768421393725)
  ·
    refine ⟨18761533810122288158022647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50030756826992768421393725 18761533810122288158022647)
    ·
      refine ⟨28142300715183432237033971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18761533810122288158022647 28142300715183432237033971)
      ·
        refine ⟨42213451072775148355550957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28142300715183432237033971 42213451072775148355550957)
        ·
          refine ⟨15830044152290680633331609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42213451072775148355550957 15830044152290680633331609)
          ·
            refine ⟨11872533114218010474998707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15830044152290680633331609 11872533114218010474998707)
            ·
              refine ⟨17808799671327015712498061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11872533114218010474998707 17808799671327015712498061)
              ·
                refine ⟨6678299876747630892186773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17808799671327015712498061 6678299876747630892186773)
                ·
                  refine ⟨313045306722545198071255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6678299876747630892186773 313045306722545198071255)
                  ·
                    rfl

theorem cell23_5486882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_5486882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486882 prefixEnd_5486882 := by exact prefixLift 5486882
  have htrace : WordTrace (prefixWord ++ tailWord_5486882) baseStart_5486882 baseEnd_5486882 := by
    simpa [prefixWord, tailWord_5486882, baseEnd_5486882] using wordTrace_append hprefix tailTrace_5486882
  have hstable : (prefixWord ++ tailWord_5486882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486882).length < 2 ^ (prefixWord ++ tailWord_5486882).sum := by decide
  have hdescent : baseEnd_5486882 < baseStart_5486882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486892 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 3]
def baseStart_5486892 : Nat := 118140960795 + 5486892 * 2 ^ 59
def prefixEnd_5486892 : Nat := 4983230072969 + 3 ^ 40 * 5486892 * 2
def baseEnd_5486892 : Nat := 2817412895309451743516249

theorem tailTrace_5486892 : CollatzResearch.WordTrace tailWord_5486892 prefixEnd_5486892 2817412895309451743516249 := by
  unfold tailWord_5486892
  simp only [CollatzResearch.WordTrace]
  refine ⟨100061696018967422696719465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133415594691956563595625953 100061696018967422696719465)
  ·
    refine ⟨75046272014225567022539599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100061696018967422696719465 75046272014225567022539599)
    ·
      refine ⟨112569408021338350533809399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75046272014225567022539599 112569408021338350533809399)
      ·
        refine ⟨168854112032007525800714099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112569408021338350533809399 168854112032007525800714099)
        ·
          refine ⟨253281168048011288701071149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168854112032007525800714099 253281168048011288701071149)
          ·
            refine ⟨94980438018004233262901681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253281168048011288701071149 94980438018004233262901681)
            ·
              refine ⟨71235328513503174947176261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94980438018004233262901681 71235328513503174947176261)
              ·
                refine ⟨13356624096281845302595549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71235328513503174947176261 13356624096281845302595549)
                ·
                  refine ⟨5008734036105691988473331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13356624096281845302595549 5008734036105691988473331)
                  ·
                    refine ⟨7513101054158537982709997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008734036105691988473331 7513101054158537982709997)
                    ·
                      refine ⟨2817412895309451743516249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513101054158537982709997 2817412895309451743516249)
                      ·
                        rfl

theorem cell23_5486892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_5486892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486892 prefixEnd_5486892 := by exact prefixLift 5486892
  have htrace : WordTrace (prefixWord ++ tailWord_5486892) baseStart_5486892 baseEnd_5486892 := by
    simpa [prefixWord, tailWord_5486892, baseEnd_5486892] using wordTrace_append hprefix tailTrace_5486892
  have hstable : (prefixWord ++ tailWord_5486892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486892).length < 2 ^ (prefixWord ++ tailWord_5486892).sum := by decide
  have hdescent : baseEnd_5486892 < baseStart_5486892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486932 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_5486932 : Nat := 118140960795 + 5486932 * 2 ^ 59
def prefixEnd_5486932 : Nat := 4983230072969 + 3 ^ 40 * 5486932 * 2
def baseEnd_5486932 : Nat := 2817433434535631587016065

theorem tailTrace_5486932 : CollatzResearch.WordTrace tailWord_5486932 prefixEnd_5486932 2817433434535631587016065 := by
  unfold tailWord_5486932
  simp only [CollatzResearch.WordTrace]
  refine ⟨100062425478894966112447525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133416567305193288149930033 100062425478894966112447525)
  ·
    refine ⟨18761704777292806146083911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100062425478894966112447525 18761704777292806146083911)
    ·
      refine ⟨28142557165939209219125867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18761704777292806146083911 28142557165939209219125867)
      ·
        refine ⟨42213835748908813828688801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28142557165939209219125867 42213835748908813828688801)
        ·
          refine ⟨31660376811681610371516601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42213835748908813828688801 31660376811681610371516601)
          ·
            refine ⟨23745282608761207778637451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31660376811681610371516601 23745282608761207778637451)
            ·
              refine ⟨35617923913141811667956177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23745282608761207778637451 35617923913141811667956177)
              ·
                refine ⟨26713442934856358750967133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35617923913141811667956177 26713442934856358750967133)
                ·
                  refine ⟨10017541100571134531612675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26713442934856358750967133 10017541100571134531612675)
                  ·
                    refine ⟨15026311650856701797419013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10017541100571134531612675 15026311650856701797419013)
                    ·
                      refine ⟨2817433434535631587016065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15026311650856701797419013 2817433434535631587016065)
                      ·
                        rfl

theorem cell23_5486932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_5486932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486932 prefixEnd_5486932 := by exact prefixLift 5486932
  have htrace : WordTrace (prefixWord ++ tailWord_5486932) baseStart_5486932 baseEnd_5486932 := by
    simpa [prefixWord, tailWord_5486932, baseEnd_5486932] using wordTrace_append hprefix tailTrace_5486932
  have hstable : (prefixWord ++ tailWord_5486932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486932).length < 2 ^ (prefixWord ++ tailWord_5486932).sum := by decide
  have hdescent : baseEnd_5486932 < baseStart_5486932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486935 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_5486935 : Nat := 118140960795 + 5486935 * 2 ^ 59
def prefixEnd_5486935 : Nat := 4983230072969 + 3 ^ 40 * 5486935 * 2
def baseEnd_5486935 : Nat := 2817434974977595075278551

theorem tailTrace_5486935 : CollatzResearch.WordTrace tailWord_5486935 prefixEnd_5486935 2817434974977595075278551 := by
  unfold tailWord_5486935
  simp only [CollatzResearch.WordTrace]
  refine ⟨200124960376779063737254259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133416640251186042491502839 200124960376779063737254259)
  ·
    refine ⟨300187440565168595605881389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200124960376779063737254259 300187440565168595605881389)
    ·
      refine ⟨112570290211938223352205521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300187440565168595605881389 112570290211938223352205521)
      ·
        refine ⟨84427717658953667514154141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112570290211938223352205521 84427717658953667514154141)
        ·
          refine ⟨31660394122107625317807803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84427717658953667514154141 31660394122107625317807803)
          ·
            refine ⟨47490591183161437976711705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31660394122107625317807803 47490591183161437976711705)
            ·
              refine ⟨35617943387371078482533779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47490591183161437976711705 35617943387371078482533779)
              ·
                refine ⟨53426915081056617723800669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35617943387371078482533779 53426915081056617723800669)
                ·
                  refine ⟨20035093155396231646425251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53426915081056617723800669 20035093155396231646425251)
                  ·
                    refine ⟨30052639733094347469637877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20035093155396231646425251 30052639733094347469637877)
                    ·
                      refine ⟨2817434974977595075278551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30052639733094347469637877 2817434974977595075278551)
                      ·
                        rfl

theorem cell23_5486935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_5486935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486935 prefixEnd_5486935 := by exact prefixLift 5486935
  have htrace : WordTrace (prefixWord ++ tailWord_5486935) baseStart_5486935 baseEnd_5486935 := by
    simpa [prefixWord, tailWord_5486935, baseEnd_5486935] using wordTrace_append hprefix tailTrace_5486935
  have hstable : (prefixWord ++ tailWord_5486935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486935).length < 2 ^ (prefixWord ++ tailWord_5486935).sum := by decide
  have hdescent : baseEnd_5486935 < baseStart_5486935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486949 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 5, 2, 2]
def baseStart_5486949 : Nat := 118140960795 + 5486949 * 2 ^ 59
def prefixEnd_5486949 : Nat := 4983230072969 + 3 ^ 40 * 5486949 * 2
def baseEnd_5486949 : Nat := 2817442163706758020503487

theorem tailTrace_5486949 : CollatzResearch.WordTrace tailWord_5486949 prefixEnd_5486949 2817442163706758020503487 := by
  unfold tailWord_5486949
  simp only [CollatzResearch.WordTrace]
  refine ⟨200125470998728344128263901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133416980665818896085509267 200125470998728344128263901)
  ·
    refine ⟨75047051624523129048098963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200125470998728344128263901 75047051624523129048098963)
    ·
      refine ⟨112570577436784693572148445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75047051624523129048098963 112570577436784693572148445)
      ·
        refine ⟨42213966538794260089555667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112570577436784693572148445 42213966538794260089555667)
        ·
          refine ⟨63320949808191390134333501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42213966538794260089555667 63320949808191390134333501)
          ·
            refine ⟨23745356178071771300375063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63320949808191390134333501 23745356178071771300375063)
            ·
              refine ⟨35618034267107656950562595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23745356178071771300375063 35618034267107656950562595)
              ·
                refine ⟨53427051400661485425843893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35618034267107656950562595 53427051400661485425843893)
                ·
                  refine ⟨5008786068812014258672865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53427051400661485425843893 5008786068812014258672865)
                  ·
                    refine ⟨3756589551609010694004649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5008786068812014258672865 3756589551609010694004649)
                    ·
                      refine ⟨2817442163706758020503487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756589551609010694004649 2817442163706758020503487)
                      ·
                        rfl

theorem cell23_5486949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_5486949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486949 prefixEnd_5486949 := by exact prefixLift 5486949
  have htrace : WordTrace (prefixWord ++ tailWord_5486949) baseStart_5486949 baseEnd_5486949 := by
    simpa [prefixWord, tailWord_5486949, baseEnd_5486949] using wordTrace_append hprefix tailTrace_5486949
  have hstable : (prefixWord ++ tailWord_5486949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486949).length < 2 ^ (prefixWord ++ tailWord_5486949).sum := by decide
  have hdescent : baseEnd_5486949 < baseStart_5486949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486962 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5486962 : Nat := 118140960795 + 5486962 * 2 ^ 59
def prefixEnd_5486962 : Nat := 4983230072969 + 3 ^ 40 * 5486962 * 2
def baseEnd_5486962 : Nat := 2817448838955266469640927

theorem tailTrace_5486962 : CollatzResearch.WordTrace tailWord_5486962 prefixEnd_5486962 2817448838955266469640927 := by
  unfold tailWord_5486962
  simp only [CollatzResearch.WordTrace]
  refine ⟨50031486286920311837121785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133417296765120831565658093 50031486286920311837121785)
  ·
    refine ⟨37523614715190233877841339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50031486286920311837121785 37523614715190233877841339)
    ·
      refine ⟨56285422072785350816762009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37523614715190233877841339 56285422072785350816762009)
      ·
        refine ⟨42214066554589013112571507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56285422072785350816762009 42214066554589013112571507)
        ·
          refine ⟨63321099831883519668857261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42214066554589013112571507 63321099831883519668857261)
          ·
            refine ⟨23745412436956319875821473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63321099831883519668857261 23745412436956319875821473)
            ·
              refine ⟨17809059327717239906866105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23745412436956319875821473 17809059327717239906866105)
              ·
                refine ⟨13356794495787929930149579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17809059327717239906866105 13356794495787929930149579)
                ·
                  refine ⟨20035191743681894895224369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13356794495787929930149579 20035191743681894895224369)
                  ·
                    refine ⟨15026393807761421171418277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20035191743681894895224369 15026393807761421171418277)
                    ·
                      refine ⟨2817448838955266469640927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15026393807761421171418277 2817448838955266469640927)
                      ·
                        rfl

theorem cell23_5486962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5486962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486962 prefixEnd_5486962 := by exact prefixLift 5486962
  have htrace : WordTrace (prefixWord ++ tailWord_5486962) baseStart_5486962 baseEnd_5486962 := by
    simpa [prefixWord, tailWord_5486962, baseEnd_5486962] using wordTrace_append hprefix tailTrace_5486962
  have hstable : (prefixWord ++ tailWord_5486962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486962).length < 2 ^ (prefixWord ++ tailWord_5486962).sum := by decide
  have hdescent : baseEnd_5486962 < baseStart_5486962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486996 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_5486996 : Nat := 118140960795 + 5486996 * 2 ^ 59
def prefixEnd_5486996 : Nat := 4983230072969 + 3 ^ 40 * 5486996 * 2
def baseEnd_5486996 : Nat := 2817466297297519336615771

theorem tailTrace_5486996 : CollatzResearch.WordTrace tailWord_5486996 prefixEnd_5486996 2817466297297519336615771 := by
  unfold tailWord_5486996
  simp only [CollatzResearch.WordTrace]
  refine ⟨100063592614779035577612421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133418123486372047436816561 100063592614779035577612421)
  ·
    refine ⟨18761923615271069170802329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100063592614779035577612421 18761923615271069170802329)
    ·
      refine ⟨14071442711453301878101747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18761923615271069170802329 14071442711453301878101747)
      ·
        refine ⟨21107164067179952817152621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14071442711453301878101747 21107164067179952817152621)
        ·
          refine ⟨7915186525192482306432233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21107164067179952817152621 7915186525192482306432233)
          ·
            refine ⟨5936389893894361729824175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7915186525192482306432233 5936389893894361729824175)
            ·
              refine ⟨8904584840841542594736263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5936389893894361729824175 8904584840841542594736263)
              ·
                refine ⟨13356877261262313892104395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8904584840841542594736263 13356877261262313892104395)
                ·
                  refine ⟨20035315891893470838156593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13356877261262313892104395 20035315891893470838156593)
                  ·
                    refine ⟨15026486918920103128617445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20035315891893470838156593 15026486918920103128617445)
                    ·
                      refine ⟨2817466297297519336615771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15026486918920103128617445 2817466297297519336615771)
                      ·
                        rfl

theorem cell23_5486996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_5486996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486996 prefixEnd_5486996 := by exact prefixLift 5486996
  have htrace : WordTrace (prefixWord ++ tailWord_5486996) baseStart_5486996 baseEnd_5486996 := by
    simpa [prefixWord, tailWord_5486996, baseEnd_5486996] using wordTrace_append hprefix tailTrace_5486996
  have hstable : (prefixWord ++ tailWord_5486996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486996).length < 2 ^ (prefixWord ++ tailWord_5486996).sum := by decide
  have hdescent : baseEnd_5486996 < baseStart_5486996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5486999 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_5486999 : Nat := 118140960795 + 5486999 * 2 ^ 59
def prefixEnd_5486999 : Nat := 4983230072969 + 3 ^ 40 * 5486999 * 2
def baseEnd_5486999 : Nat := 2817467837739482824878257

theorem tailTrace_5486999 : CollatzResearch.WordTrace tailWord_5486999 prefixEnd_5486999 2817467837739482824878257 := by
  unfold tailWord_5486999
  simp only [CollatzResearch.WordTrace]
  refine ⟨200127294648547202667584051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133418196432364801778389367 200127294648547202667584051)
  ·
    refine ⟨300190941972820804001376077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200127294648547202667584051 300190941972820804001376077)
    ·
      refine ⟨112571603239807801500516029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 300190941972820804001376077 112571603239807801500516029)
      ·
        refine ⟨42214351214927925562693511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112571603239807801500516029 42214351214927925562693511)
        ·
          refine ⟨63321526822391888344040267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42214351214927925562693511 63321526822391888344040267)
          ·
            refine ⟨94982290233587832516060401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63321526822391888344040267 94982290233587832516060401)
            ·
              refine ⟨71236717675190874387045301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94982290233587832516060401 71236717675190874387045301)
              ·
                refine ⟨6678442282049144473785497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71236717675190874387045301 6678442282049144473785497)
                ·
                  refine ⟨5008831711536858355339123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6678442282049144473785497 5008831711536858355339123)
                  ·
                    refine ⟨7513247567305287533008685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008831711536858355339123 7513247567305287533008685)
                    ·
                      refine ⟨2817467837739482824878257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513247567305287533008685 2817467837739482824878257)
                      ·
                        rfl

theorem cell23_5486999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_5486999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5486999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5486999 prefixEnd_5486999 := by exact prefixLift 5486999
  have htrace : WordTrace (prefixWord ++ tailWord_5486999) baseStart_5486999 baseEnd_5486999 := by
    simpa [prefixWord, tailWord_5486999, baseEnd_5486999] using wordTrace_append hprefix tailTrace_5486999
  have hstable : (prefixWord ++ tailWord_5486999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5486999).length < 2 ^ (prefixWord ++ tailWord_5486999).sum := by decide
  have hdescent : baseEnd_5486999 < baseStart_5486999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5486999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487006 : List Nat := [4, 3, 1, 2, 1, 3, 2, 7]
def baseStart_5487006 : Nat := 118140960795 + 5487006 * 2 ^ 59
def prefixEnd_5487006 : Nat := 4983230072969 + 3 ^ 40 * 5487006 * 2
def baseEnd_5487006 : Nat := 104350793781632011018175

theorem tailTrace_5487006 : CollatzResearch.WordTrace tailWord_5487006 prefixEnd_5487006 104350793781632011018175 := by
  unfold tailWord_5487006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25015943744940230357886109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133418366639681228575392581 25015943744940230357886109)
  ·
    refine ⟨9380978904352586384207291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25015943744940230357886109 9380978904352586384207291)
    ·
      refine ⟨14071468356528879576310937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9380978904352586384207291 14071468356528879576310937)
      ·
        refine ⟨10553601267396659682233203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14071468356528879576310937 10553601267396659682233203)
        ·
          refine ⟨15830401901094989523349805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10553601267396659682233203 15830401901094989523349805)
          ·
            refine ⟨5936400712910621071256177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15830401901094989523349805 5936400712910621071256177)
            ·
              refine ⟨4452300534682965803442133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5936400712910621071256177 4452300534682965803442133)
              ·
                refine ⟨104350793781632011018175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4452300534682965803442133 104350793781632011018175)
                ·
                  rfl

theorem cell23_5487006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_5487006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487006 prefixEnd_5487006 := by exact prefixLift 5487006
  have htrace : WordTrace (prefixWord ++ tailWord_5487006) baseStart_5487006 baseEnd_5487006 := by
    simpa [prefixWord, tailWord_5487006, baseEnd_5487006] using wordTrace_append hprefix tailTrace_5487006
  have hstable : (prefixWord ++ tailWord_5487006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487006).length < 2 ^ (prefixWord ++ tailWord_5487006).sum := by decide
  have hdescent : baseEnd_5487006 < baseStart_5487006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487016 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5487016 : Nat := 118140960795 + 5487016 * 2 ^ 59
def prefixEnd_5487016 : Nat := 4983230072969 + 3 ^ 40 * 5487016 * 2
def baseEnd_5487016 : Nat := 2817476566910609258365679

theorem tailTrace_5487016 : CollatzResearch.WordTrace tailWord_5487016 prefixEnd_5487016 2817476566910609258365679 := by
  unfold tailWord_5487016
  simp only [CollatzResearch.WordTrace]
  refine ⟨100063957344742807285476451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133418609792990409713968601 100063957344742807285476451)
  ·
    refine ⟨150095936017114210928214677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100063957344742807285476451 150095936017114210928214677)
    ·
      refine ⟨7035747000802228637260063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150095936017114210928214677 7035747000802228637260063)
      ·
        refine ⟨10553620501203342955890095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035747000802228637260063 10553620501203342955890095)
        ·
          refine ⟨15830430751805014433835143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10553620501203342955890095 15830430751805014433835143)
          ·
            refine ⟨23745646127707521650752715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15830430751805014433835143 23745646127707521650752715)
            ·
              refine ⟨35618469191561282476129073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23745646127707521650752715 35618469191561282476129073)
              ·
                refine ⟨26713851893670961857096805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35618469191561282476129073 26713851893670961857096805)
                ·
                  refine ⟨5008847230063305348205651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26713851893670961857096805 5008847230063305348205651)
                  ·
                    refine ⟨7513270845094958022308477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5008847230063305348205651 7513270845094958022308477)
                    ·
                      refine ⟨2817476566910609258365679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513270845094958022308477 2817476566910609258365679)
                      ·
                        rfl

theorem cell23_5487016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5487016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487016 prefixEnd_5487016 := by exact prefixLift 5487016
  have htrace : WordTrace (prefixWord ++ tailWord_5487016) baseStart_5487016 baseEnd_5487016 := by
    simpa [prefixWord, tailWord_5487016, baseEnd_5487016] using wordTrace_append hprefix tailTrace_5487016
  have hstable : (prefixWord ++ tailWord_5487016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487016).length < 2 ^ (prefixWord ++ tailWord_5487016).sum := by decide
  have hdescent : baseEnd_5487016 < baseStart_5487016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487035 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4]
def baseStart_5487035 : Nat := 118140960795 + 5487035 * 2 ^ 59
def prefixEnd_5487035 : Nat := 4983230072969 + 3 ^ 40 * 5487035 * 2
def baseEnd_5487035 : Nat := 2817486323043044684028091

theorem tailTrace_5487035 : CollatzResearch.WordTrace tailWord_5487035 prefixEnd_5487035 2817486323043044684028091 := by
  unfold tailWord_5487035
  simp only [CollatzResearch.WordTrace]
  refine ⟨200128607676416780815894559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133419071784277853877263039 200128607676416780815894559)
  ·
    refine ⟨300192911514625171223841839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200128607676416780815894559 300192911514625171223841839)
    ·
      refine ⟨450289367271937756835762759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300192911514625171223841839 450289367271937756835762759)
      ·
        refine ⟨675434050907906635253644139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450289367271937756835762759 675434050907906635253644139)
        ·
          refine ⟨1013151076361859952880466209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675434050907906635253644139 1013151076361859952880466209)
          ·
            refine ⟨759863307271394964660349657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013151076361859952880466209 759863307271394964660349657)
            ·
              refine ⟨569897480453546223495262243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759863307271394964660349657 569897480453546223495262243)
              ·
                refine ⟨854846220680319335242893365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569897480453546223495262243 854846220680319335242893365)
                ·
                  refine ⟨80141833188779937679021253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854846220680319335242893365 80141833188779937679021253)
                  ·
                    refine ⟨15026593722896238314816485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80141833188779937679021253 15026593722896238314816485)
                    ·
                      refine ⟨2817486323043044684028091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15026593722896238314816485 2817486323043044684028091)
                      ·
                        rfl

theorem cell23_5487035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_5487035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487035 prefixEnd_5487035 := by exact prefixLift 5487035
  have htrace : WordTrace (prefixWord ++ tailWord_5487035) baseStart_5487035 baseEnd_5487035 := by
    simpa [prefixWord, tailWord_5487035, baseEnd_5487035] using wordTrace_append hprefix tailTrace_5487035
  have hstable : (prefixWord ++ tailWord_5487035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487035).length < 2 ^ (prefixWord ++ tailWord_5487035).sum := by decide
  have hdescent : baseEnd_5487035 < baseStart_5487035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487079 : List Nat := [1, 1, 5, 2, 1, 1, 2, 5, 5]
def baseStart_5487079 : Nat := 118140960795 + 5487079 * 2 ^ 59
def prefixEnd_5487079 : Nat := 4983230072969 + 3 ^ 40 * 5487079 * 2
def baseEnd_5487079 : Nat := 313056546243538056875321

theorem tailTrace_5487079 : CollatzResearch.WordTrace tailWord_5487079 prefixEnd_5487079 313056546243538056875321 := by
  unfold tailWord_5487079
  simp only [CollatzResearch.WordTrace]
  refine ⟨200130212488257376330496291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133420141658838250886997527 200130212488257376330496291)
  ·
    refine ⟨300195318732386064495744437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200130212488257376330496291 300195318732386064495744437)
    ·
      refine ⟨28143311131161193546476041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 300195318732386064495744437 28143311131161193546476041)
      ·
        refine ⟨21107483348370895159857031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28143311131161193546476041 21107483348370895159857031)
        ·
          refine ⟨31661225022556342739785547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21107483348370895159857031 31661225022556342739785547)
          ·
            refine ⟨47491837533834514109678321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31661225022556342739785547 47491837533834514109678321)
            ·
              refine ⟨35618878150375885582258741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47491837533834514109678321 35618878150375885582258741)
              ·
                refine ⟨3339269826597739273336757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35618878150375885582258741 3339269826597739273336757)
                ·
                  refine ⟨313056546243538056875321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3339269826597739273336757 313056546243538056875321)
                  ·
                    rfl

theorem cell23_5487079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 5].length) (baseStart_5487079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487079 prefixEnd_5487079 := by exact prefixLift 5487079
  have htrace : WordTrace (prefixWord ++ tailWord_5487079) baseStart_5487079 baseEnd_5487079 := by
    simpa [prefixWord, tailWord_5487079, baseEnd_5487079] using wordTrace_append hprefix tailTrace_5487079
  have hstable : (prefixWord ++ tailWord_5487079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487079).length < 2 ^ (prefixWord ++ tailWord_5487079).sum := by decide
  have hdescent : baseEnd_5487079 < baseStart_5487079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487090 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_5487090 : Nat := 118140960795 + 5487090 * 2 ^ 59
def prefixEnd_5487090 : Nat := 4983230072969 + 3 ^ 40 * 5487090 * 2
def baseEnd_5487090 : Nat := 2817514564479041968840339

theorem tailTrace_5487090 : CollatzResearch.WordTrace tailWord_5487090 prefixEnd_5487090 2817514564479041968840339 := by
  unfold tailWord_5487090
  simp only [CollatzResearch.WordTrace]
  refine ⟨50032653422804381302286681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133420409127478350139431149 50032653422804381302286681)
  ·
    refine ⟨37524490067103285976715011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50032653422804381302286681 37524490067103285976715011)
    ·
      refine ⟨56286735100654928965072517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37524490067103285976715011 56286735100654928965072517)
      ·
        refine ⟨10553762831372799180951097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56286735100654928965072517 10553762831372799180951097)
        ·
          refine ⟨7915322123529599385713323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10553762831372799180951097 7915322123529599385713323)
          ·
            refine ⟨11872983185294399078569985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7915322123529599385713323 11872983185294399078569985)
            ·
              refine ⟨8904737388970799308927489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11872983185294399078569985 8904737388970799308927489)
              ·
                refine ⟨6678553041728099481695617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8904737388970799308927489 6678553041728099481695617)
                ·
                  refine ⟨5008914781296074611271713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6678553041728099481695617 5008914781296074611271713)
                  ·
                    refine ⟨3756686085972055958453785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5008914781296074611271713 3756686085972055958453785)
                    ·
                      refine ⟨2817514564479041968840339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756686085972055958453785 2817514564479041968840339)
                      ·
                        rfl

theorem cell23_5487090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_5487090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487090 prefixEnd_5487090 := by exact prefixLift 5487090
  have htrace : WordTrace (prefixWord ++ tailWord_5487090) baseStart_5487090 baseEnd_5487090 := by
    simpa [prefixWord, tailWord_5487090, baseEnd_5487090] using wordTrace_append hprefix tailTrace_5487090
  have hstable : (prefixWord ++ tailWord_5487090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487090).length < 2 ^ (prefixWord ++ tailWord_5487090).sum := by decide
  have hdescent : baseEnd_5487090 < baseStart_5487090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487112 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_5487112 : Nat := 118140960795 + 5487112 * 2 ^ 59
def prefixEnd_5487112 : Nat := 4983230072969 + 3 ^ 40 * 5487112 * 2
def baseEnd_5487112 : Nat := 2817525861053440882765237

theorem tailTrace_5487112 : CollatzResearch.WordTrace tailWord_5487112 prefixEnd_5487112 2817525861053440882765237 := by
  unfold tailWord_5487112
  simp only [CollatzResearch.WordTrace]
  refine ⟨100065708048568911483223795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133420944064758548644298393 100065708048568911483223795)
  ·
    refine ⟨150098562072853367224835693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100065708048568911483223795 150098562072853367224835693)
    ·
      refine ⟨56286960777320012709313385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 150098562072853367224835693 56286960777320012709313385)
      ·
        refine ⟨42215220582990009531985039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56286960777320012709313385 42215220582990009531985039)
        ·
          refine ⟨63322830874485014297977559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42215220582990009531985039 63322830874485014297977559)
          ·
            refine ⟨94984246311727521446966339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63322830874485014297977559 94984246311727521446966339)
            ·
              refine ⟨142476369467591282170449509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94984246311727521446966339 142476369467591282170449509)
              ·
                refine ⟨26714319275173365406959283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142476369467591282170449509 26714319275173365406959283)
                ·
                  refine ⟨40071478912760048110438925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26714319275173365406959283 40071478912760048110438925)
                  ·
                    refine ⟨15026804592285018041414597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40071478912760048110438925 15026804592285018041414597)
                    ·
                      refine ⟨2817525861053440882765237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15026804592285018041414597 2817525861053440882765237)
                      ·
                        rfl

theorem cell23_5487112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_5487112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487112 prefixEnd_5487112 := by exact prefixLift 5487112
  have htrace : WordTrace (prefixWord ++ tailWord_5487112) baseStart_5487112 baseEnd_5487112 := by
    simpa [prefixWord, tailWord_5487112, baseEnd_5487112] using wordTrace_append hprefix tailTrace_5487112
  have hstable : (prefixWord ++ tailWord_5487112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487112).length < 2 ^ (prefixWord ++ tailWord_5487112).sum := by decide
  have hdescent : baseEnd_5487112 < baseStart_5487112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487146 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5487146 : Nat := 118140960795 + 5487146 * 2 ^ 59
def prefixEnd_5487146 : Nat := 4983230072969 + 3 ^ 40 * 5487146 * 2
def baseEnd_5487146 : Nat := 2817543319395693749740081

theorem tailTrace_5487146 : CollatzResearch.WordTrace tailWord_5487146 prefixEnd_5487146 2817543319395693749740081 := by
  unfold tailWord_5487146
  simp only [CollatzResearch.WordTrace]
  refine ⟨50033164044753661693296323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133421770786009764515456861 50033164044753661693296323)
  ·
    refine ⟨75049746067130492539944485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50033164044753661693296323 75049746067130492539944485)
    ·
      refine ⟨14071827387586967351239591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75049746067130492539944485 14071827387586967351239591)
      ·
        refine ⟨21107741081380451026859387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14071827387586967351239591 21107741081380451026859387)
        ·
          refine ⟨31661611622070676540289081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21107741081380451026859387 31661611622070676540289081)
          ·
            refine ⟨23746208716553007405216811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31661611622070676540289081 23746208716553007405216811)
            ·
              refine ⟨35619313074829511107825217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23746208716553007405216811 35619313074829511107825217)
              ·
                refine ⟨26714484806122133330868913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35619313074829511107825217 26714484806122133330868913)
                ·
                  refine ⟨20035863604591599998151685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26714484806122133330868913 20035863604591599998151685)
                  ·
                    refine ⟨3756724425860924999653441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20035863604591599998151685 3756724425860924999653441)
                    ·
                      refine ⟨2817543319395693749740081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756724425860924999653441 2817543319395693749740081)
                      ·
                        rfl

theorem cell23_5487146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5487146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487146 prefixEnd_5487146 := by exact prefixLift 5487146
  have htrace : WordTrace (prefixWord ++ tailWord_5487146) baseStart_5487146 baseEnd_5487146 := by
    simpa [prefixWord, tailWord_5487146, baseEnd_5487146] using wordTrace_append hprefix tailTrace_5487146
  have hstable : (prefixWord ++ tailWord_5487146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487146).length < 2 ^ (prefixWord ++ tailWord_5487146).sum := by decide
  have hdescent : baseEnd_5487146 < baseStart_5487146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487213 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_5487213 : Nat := 118140960795 + 5487213 * 2 ^ 59
def prefixEnd_5487213 : Nat := 4983230072969 + 3 ^ 40 * 5487213 * 2
def baseEnd_5487213 : Nat := 2817577722599544987602273

theorem tailTrace_5487213 : CollatzResearch.WordTrace tailWord_5487213 prefixEnd_5487213 2817577722599544987602273 := by
  unfold tailWord_5487213
  simp only [CollatzResearch.WordTrace]
  refine ⟨200135099869771917215874293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133423399913181278143916195 200135099869771917215874293)
  ·
    refine ⟨18762665612791117238988215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 200135099869771917215874293 18762665612791117238988215)
    ·
      refine ⟨28143998419186675858482323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18762665612791117238988215 28143998419186675858482323)
      ·
        refine ⟨42215997628780013787723485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28143998419186675858482323 42215997628780013787723485)
        ·
          refine ⟨15830999110792505170396307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42215997628780013787723485 15830999110792505170396307)
          ·
            refine ⟨23746498666188757755594461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15830999110792505170396307 23746498666188757755594461)
            ·
              refine ⟨8904936999820784158347923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23746498666188757755594461 8904936999820784158347923)
              ·
                refine ⟨13357405499731176237521885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8904936999820784158347923 13357405499731176237521885)
                ·
                  refine ⟨5009027062399191089070707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13357405499731176237521885 5009027062399191089070707)
                  ·
                    refine ⟨7513540593598786633606061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009027062399191089070707 7513540593598786633606061)
                    ·
                      refine ⟨2817577722599544987602273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513540593598786633606061 2817577722599544987602273)
                      ·
                        rfl

theorem cell23_5487213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_5487213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487213 prefixEnd_5487213 := by exact prefixLift 5487213
  have htrace : WordTrace (prefixWord ++ tailWord_5487213) baseStart_5487213 baseEnd_5487213 := by
    simpa [prefixWord, tailWord_5487213, baseEnd_5487213] using wordTrace_append hprefix tailTrace_5487213
  have hstable : (prefixWord ++ tailWord_5487213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487213).length < 2 ^ (prefixWord ++ tailWord_5487213).sum := by decide
  have hdescent : baseEnd_5487213 < baseStart_5487213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487219 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 2, 6, 2]
def baseStart_5487219 : Nat := 118140960795 + 5487219 * 2 ^ 59
def prefixEnd_5487219 : Nat := 4983230072969 + 3 ^ 40 * 5487219 * 2
def baseEnd_5487219 : Nat := 2817580803483471964127245

theorem tailTrace_5487219 : CollatzResearch.WordTrace tailWord_5487219 prefixEnd_5487219 2817580803483471964127245 := by
  unfold tailWord_5487219
  simp only [CollatzResearch.WordTrace]
  refine ⟨200135318707750180240592711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133423545805166786827061807 200135318707750180240592711)
  ·
    refine ⟨300202978061625270360889067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200135318707750180240592711 300202978061625270360889067)
    ·
      refine ⟨450304467092437905541333601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300202978061625270360889067 450304467092437905541333601)
      ·
        refine ⟨337728350319328429156000201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450304467092437905541333601 337728350319328429156000201)
        ·
          refine ⟨253296262739496321867000151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337728350319328429156000201 253296262739496321867000151)
          ·
            refine ⟨379944394109244482800500227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253296262739496321867000151 379944394109244482800500227)
            ·
              refine ⟨569916591163866724200750341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379944394109244482800500227 569916591163866724200750341)
              ·
                refine ⟨106859360843225010787640689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569916591163866724200750341 106859360843225010787640689)
                ·
                  refine ⟨80144520632418758090730517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106859360843225010787640689 80144520632418758090730517)
                  ·
                    refine ⟨3756774404644629285502993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80144520632418758090730517 3756774404644629285502993)
                    ·
                      refine ⟨2817580803483471964127245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3756774404644629285502993 2817580803483471964127245)
                      ·
                        rfl

theorem cell23_5487219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 6, 2].length) (baseStart_5487219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487219 prefixEnd_5487219 := by exact prefixLift 5487219
  have htrace : WordTrace (prefixWord ++ tailWord_5487219) baseStart_5487219 baseEnd_5487219 := by
    simpa [prefixWord, tailWord_5487219, baseEnd_5487219] using wordTrace_append hprefix tailTrace_5487219
  have hstable : (prefixWord ++ tailWord_5487219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487219).length < 2 ^ (prefixWord ++ tailWord_5487219).sum := by decide
  have hdescent : baseEnd_5487219 < baseStart_5487219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487236 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_5487236 : Nat := 118140960795 + 5487236 * 2 ^ 59
def prefixEnd_5487236 : Nat := 4983230072969 + 3 ^ 40 * 5487236 * 2
def baseEnd_5487236 : Nat := 2817589532654598397614667

theorem tailTrace_5487236 : CollatzResearch.WordTrace tailWord_5487236 prefixEnd_5487236 2817589532654598397614667 := by
  unfold tailWord_5487236
  simp only [CollatzResearch.WordTrace]
  refine ⟨100067969374344296071980781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133423959165792394762641041 100067969374344296071980781)
  ·
    refine ⟨37525488515379111026992793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100067969374344296071980781 37525488515379111026992793)
    ·
      refine ⟨28144116386534333270244595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37525488515379111026992793 28144116386534333270244595)
      ·
        refine ⟨42216174579801499905366893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28144116386534333270244595 42216174579801499905366893)
        ·
          refine ⟨15831065467425562464512585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42216174579801499905366893 15831065467425562464512585)
          ·
            refine ⟨11873299100569171848384439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15831065467425562464512585 11873299100569171848384439)
            ·
              refine ⟨17809948650853757772576659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11873299100569171848384439 17809948650853757772576659)
              ·
                refine ⟨26714922976280636658864989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17809948650853757772576659 26714922976280636658864989)
                ·
                  refine ⟨10018096116105238747074371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26714922976280636658864989 10018096116105238747074371)
                  ·
                    refine ⟨15027144174157858120611557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10018096116105238747074371 15027144174157858120611557)
                    ·
                      refine ⟨2817589532654598397614667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15027144174157858120611557 2817589532654598397614667)
                      ·
                        rfl

theorem cell23_5487236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_5487236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487236 prefixEnd_5487236 := by exact prefixLift 5487236
  have htrace : WordTrace (prefixWord ++ tailWord_5487236) baseStart_5487236 baseEnd_5487236 := by
    simpa [prefixWord, tailWord_5487236, baseEnd_5487236] using wordTrace_append hprefix tailTrace_5487236
  have hstable : (prefixWord ++ tailWord_5487236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487236).length < 2 ^ (prefixWord ++ tailWord_5487236).sum := by decide
  have hdescent : baseEnd_5487236 < baseStart_5487236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5487264 : List Nat := [2, 1, 1, 4, 5, 1, 2, 2, 1, 1, 3]
def baseStart_5487264 : Nat := 118140960795 + 5487264 * 2 ^ 59
def prefixEnd_5487264 : Nat := 4983230072969 + 3 ^ 40 * 5487264 * 2
def baseEnd_5487264 : Nat := 2817603910112924288064539

theorem tailTrace_5487264 : CollatzResearch.WordTrace tailWord_5487264 prefixEnd_5487264 2817603910112924288064539 := by
  unfold tailWord_5487264
  simp only [CollatzResearch.WordTrace]
  refine ⟨100068479996293576462990423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133424639995058101950653897 100068479996293576462990423)
  ·
    refine ⟨150102719994440364694485635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100068479996293576462990423 150102719994440364694485635)
    ·
      refine ⟨225154079991660547041728453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150102719994440364694485635 225154079991660547041728453)
      ·
        refine ⟨42216389998436352570324085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225154079991660547041728453 42216389998436352570324085)
        ·
          refine ⟨3957786562353408053467883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42216389998436352570324085 3957786562353408053467883)
          ·
            refine ⟨5936679843530112080201825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957786562353408053467883 5936679843530112080201825)
            ·
              refine ⟨4452509882647584060151369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5936679843530112080201825 4452509882647584060151369)
              ·
                refine ⟨3339382411985688045113527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4452509882647584060151369 3339382411985688045113527)
                ·
                  refine ⟨5009073617978532067670291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3339382411985688045113527 5009073617978532067670291)
                  ·
                    refine ⟨7513610426967798101505437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5009073617978532067670291 7513610426967798101505437)
                    ·
                      refine ⟨2817603910112924288064539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7513610426967798101505437 2817603910112924288064539)
                      ·
                        rfl

theorem cell23_5487264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_5487264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5487264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5487264 prefixEnd_5487264 := by exact prefixLift 5487264
  have htrace : WordTrace (prefixWord ++ tailWord_5487264) baseStart_5487264 baseEnd_5487264 := by
    simpa [prefixWord, tailWord_5487264, baseEnd_5487264] using wordTrace_append hprefix tailTrace_5487264
  have hstable : (prefixWord ++ tailWord_5487264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5487264).length < 2 ^ (prefixWord ++ tailWord_5487264).sum := by decide
  have hdescent : baseEnd_5487264 < baseStart_5487264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5487264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
