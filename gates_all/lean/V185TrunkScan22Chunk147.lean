import V185TrunkScan22Chunk146

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1315083 : List Nat := [1, 1, 1, 1, 5, 2, 3, 4, 1, 3]
def baseStart_1315083 : Nat := 118140960795 + 1315083 * 2 ^ 59
def prefixEnd_1315083 : Nat := 4983230072969 + 3 ^ 40 * 1315083 * 2
def baseEnd_1315083 : Nat := 450179786371188976943033

theorem tailTrace_1315083 : CollatzResearch.WordTrace tailWord_1315083 prefixEnd_1315083 450179786371188976943033 := by
  unfold tailWord_1315083
  simp only [CollatzResearch.WordTrace]
  refine ⟨47965017494686364140325903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31976678329790909426883935 47965017494686364140325903)
  ·
    refine ⟨71947526242029546210488855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47965017494686364140325903 71947526242029546210488855)
    ·
      refine ⟨107921289363044319315733283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71947526242029546210488855 107921289363044319315733283)
      ·
        refine ⟨161881934044566478973599925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107921289363044319315733283 161881934044566478973599925)
        ·
          refine ⟨15176431316678107403774993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161881934044566478973599925 15176431316678107403774993)
          ·
            refine ⟨11382323487508580552831245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15176431316678107403774993 11382323487508580552831245)
            ·
              refine ⟨4268371307815717707311717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11382323487508580552831245 4268371307815717707311717)
              ·
                refine ⟨800319620215447070120947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4268371307815717707311717 800319620215447070120947)
                ·
                  refine ⟨1200479430323170605181421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800319620215447070120947 1200479430323170605181421)
                  ·
                    refine ⟨450179786371188976943033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200479430323170605181421 450179786371188976943033)
                    ·
                      rfl

theorem cell22_1315083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 3].length) (baseStart_1315083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315083 prefixEnd_1315083 := by exact prefixLift 1315083
  have htrace : WordTrace (prefixWord ++ tailWord_1315083) baseStart_1315083 baseEnd_1315083 := by
    simpa [prefixWord, tailWord_1315083, baseEnd_1315083] using wordTrace_append hprefix tailTrace_1315083
  have hstable : (prefixWord ++ tailWord_1315083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315083).length < 2 ^ (prefixWord ++ tailWord_1315083).sum := by decide
  have hdescent : baseEnd_1315083 < baseStart_1315083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315139 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 3, 5]
def baseStart_1315139 : Nat := 118140960795 + 1315139 * 2 ^ 59
def prefixEnd_1315139 : Nat := 4983230072969 + 3 ^ 40 * 1315139 * 2
def baseEnd_1315139 : Nat := 450198956315623497542861

theorem tailTrace_1315139 : CollatzResearch.WordTrace tailWord_1315139 prefixEnd_1315139 450198956315623497542861 := by
  unfold tailWord_1315139
  simp only [CollatzResearch.WordTrace]
  refine ⟨47967059982483485704364471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31978039988322323802909647 47967059982483485704364471)
  ·
    refine ⟨71950589973725228556546707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47967059982483485704364471 71950589973725228556546707)
    ·
      refine ⟨107925884960587842834820061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71950589973725228556546707 107925884960587842834820061)
      ·
        refine ⟨40472206860220441063057523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107925884960587842834820061 40472206860220441063057523)
        ·
          refine ⟨60708310290330661594586285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40472206860220441063057523 60708310290330661594586285)
          ·
            refine ⟨22765616358873998097969857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60708310290330661594586285 22765616358873998097969857)
            ·
              refine ⟨17074212269155498573477393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22765616358873998097969857 17074212269155498573477393)
              ·
                refine ⟨12805659201866623930108045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17074212269155498573477393 12805659201866623930108045)
                ·
                  refine ⟨4802122200699983973790517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12805659201866623930108045 4802122200699983973790517)
                  ·
                    refine ⟨450198956315623497542861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4802122200699983973790517 450198956315623497542861)
                    ·
                      rfl

theorem cell22_1315139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_1315139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315139 prefixEnd_1315139 := by exact prefixLift 1315139
  have htrace : WordTrace (prefixWord ++ tailWord_1315139) baseStart_1315139 baseEnd_1315139 := by
    simpa [prefixWord, tailWord_1315139, baseEnd_1315139] using wordTrace_append hprefix tailTrace_1315139
  have hstable : (prefixWord ++ tailWord_1315139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315139).length < 2 ^ (prefixWord ++ tailWord_1315139).sum := by decide
  have hdescent : baseEnd_1315139 < baseStart_1315139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315171 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 2, 4]
def baseStart_1315171 : Nat := 118140960795 + 1315171 * 2 ^ 59
def prefixEnd_1315171 : Nat := 4983230072969 + 3 ^ 40 * 1315171 * 2
def baseEnd_1315171 : Nat := 450209910569586080742763

theorem tailTrace_1315171 : CollatzResearch.WordTrace tailWord_1315171 prefixEnd_1315171 450209910569586080742763 := by
  unfold tailWord_1315171
  simp only [CollatzResearch.WordTrace]
  refine ⟨47968227118367555169529367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31978818078911703446352911 47968227118367555169529367)
  ·
    refine ⟨71952340677551332754294051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47968227118367555169529367 71952340677551332754294051)
    ·
      refine ⟨107928511016326999131441077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71952340677551332754294051 107928511016326999131441077)
      ·
        refine ⟨10118297907780656168572601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107928511016326999131441077 10118297907780656168572601)
        ·
          refine ⟨7588723430835492126429451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10118297907780656168572601 7588723430835492126429451)
          ·
            refine ⟨11383085146253238189644177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7588723430835492126429451 11383085146253238189644177)
            ·
              refine ⟨8537313859689928642233133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11383085146253238189644177 8537313859689928642233133)
              ·
                refine ⟨3201492697383723240837425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8537313859689928642233133 3201492697383723240837425)
                ·
                  refine ⟨2401119523037792430628069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201492697383723240837425 2401119523037792430628069)
                  ·
                    refine ⟨450209910569586080742763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401119523037792430628069 450209910569586080742763)
                    ·
                      rfl

theorem cell22_1315171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_1315171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315171 prefixEnd_1315171 := by exact prefixLift 1315171
  have htrace : WordTrace (prefixWord ++ tailWord_1315171) baseStart_1315171 baseEnd_1315171 := by
    simpa [prefixWord, tailWord_1315171, baseEnd_1315171] using wordTrace_append hprefix tailTrace_1315171
  have hstable : (prefixWord ++ tailWord_1315171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315171).length < 2 ^ (prefixWord ++ tailWord_1315171).sum := by decide
  have hdescent : baseEnd_1315171 < baseStart_1315171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315175 : List Nat := [1, 1, 5, 1, 3, 3, 1, 3, 4]
def baseStart_1315175 : Nat := 118140960795 + 1315175 * 2 ^ 59
def prefixEnd_1315175 : Nat := 4983230072969 + 3 ^ 40 * 1315175 * 2
def baseEnd_1315175 : Nat := 150070426617110467880917

theorem tailTrace_1315175 : CollatzResearch.WordTrace tailWord_1315175 prefixEnd_1315175 150070426617110467880917 := by
  unfold tailWord_1315175
  simp only [CollatzResearch.WordTrace]
  refine ⟨47968373010353063852674979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31978915340235375901783319 47968373010353063852674979)
  ·
    refine ⟨71952559515529595779012469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47968373010353063852674979 71952559515529595779012469)
    ·
      refine ⟨6745552454580899604282419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71952559515529595779012469 6745552454580899604282419)
      ·
        refine ⟨10118328681871349406423629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6745552454580899604282419 10118328681871349406423629)
        ·
          refine ⟨3794373255701756027408861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10118328681871349406423629 3794373255701756027408861)
          ·
            refine ⟨1422889970888158510278323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3794373255701756027408861 1422889970888158510278323)
            ·
              refine ⟨2134334956332237765417485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422889970888158510278323 2134334956332237765417485)
              ·
                refine ⟨800375608624589162031557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2134334956332237765417485 800375608624589162031557)
                ·
                  refine ⟨150070426617110467880917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 800375608624589162031557 150070426617110467880917)
                  ·
                    rfl

theorem cell22_1315175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 4].length) (baseStart_1315175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315175 prefixEnd_1315175 := by exact prefixLift 1315175
  have htrace : WordTrace (prefixWord ++ tailWord_1315175) baseStart_1315175 baseEnd_1315175 := by
    simpa [prefixWord, tailWord_1315175, baseEnd_1315175] using wordTrace_append hprefix tailTrace_1315175
  have hstable : (prefixWord ++ tailWord_1315175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315175).length < 2 ^ (prefixWord ++ tailWord_1315175).sum := by decide
  have hdescent : baseEnd_1315175 < baseStart_1315175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315186 : List Nat := [3, 2, 1, 2, 1, 5, 8]
def baseStart_1315186 : Nat := 118140960795 + 1315186 * 2 ^ 59
def prefixEnd_1315186 : Nat := 4983230072969 + 3 ^ 40 * 1315186 * 2
def baseEnd_1315186 : Nat := 16674631310227075615471

theorem tailTrace_1315186 : CollatzResearch.WordTrace tailWord_1315186 prefixEnd_1315186 16674631310227075615471 := by
  unfold tailWord_1315186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11992193553328303182831353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31979182808875475154216941 11992193553328303182831353)
  ·
    refine ⟨8994145164996227387123515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11992193553328303182831353 8994145164996227387123515)
    ·
      refine ⟨13491217747494341080685273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8994145164996227387123515 13491217747494341080685273)
      ·
        refine ⟨10118413310620755810513955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13491217747494341080685273 10118413310620755810513955)
        ·
          refine ⟨15177619965931133715770933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10118413310620755810513955 15177619965931133715770933)
          ·
            refine ⟨1422901871806043785853525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15177619965931133715770933 1422901871806043785853525)
            ·
              refine ⟨16674631310227075615471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1422901871806043785853525 16674631310227075615471)
              ·
                rfl

theorem cell22_1315186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 8].length) (baseStart_1315186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315186 prefixEnd_1315186 := by exact prefixLift 1315186
  have htrace : WordTrace (prefixWord ++ tailWord_1315186) baseStart_1315186 baseEnd_1315186 := by
    simpa [prefixWord, tailWord_1315186, baseEnd_1315186] using wordTrace_append hprefix tailTrace_1315186
  have hstable : (prefixWord ++ tailWord_1315186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315186).length < 2 ^ (prefixWord ++ tailWord_1315186).sum := by decide
  have hdescent : baseEnd_1315186 < baseStart_1315186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315199 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 8]
def baseStart_1315199 : Nat := 118140960795 + 1315199 * 2 ^ 59
def prefixEnd_1315199 : Nat := 4983230072969 + 3 ^ 40 * 1315199 * 2
def baseEnd_1315199 : Nat := 450219495541803341042677

theorem tailTrace_1315199 : CollatzResearch.WordTrace tailWord_1315199 prefixEnd_1315199 450219495541803341042677 := by
  unfold tailWord_1315199
  simp only [CollatzResearch.WordTrace]
  refine ⟨47969248362266115951548651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31979498908177410634365767 47969248362266115951548651)
  ·
    refine ⟨71953872543399173927322977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47969248362266115951548651 71953872543399173927322977)
    ·
      refine ⟨53965404407549380445492233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71953872543399173927322977 53965404407549380445492233)
      ·
        refine ⟨40474053305662035334119175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53965404407549380445492233 40474053305662035334119175)
        ·
          refine ⟨60711079958493053001178763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40474053305662035334119175 60711079958493053001178763)
          ·
            refine ⟨91066619937739579501768145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60711079958493053001178763 91066619937739579501768145)
            ·
              refine ⟨68299964953304684626326109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91066619937739579501768145 68299964953304684626326109)
              ·
                refine ⟨25612486857489256734872291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68299964953304684626326109 25612486857489256734872291)
                ·
                  refine ⟨38418730286233885102308437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25612486857489256734872291 38418730286233885102308437)
                  ·
                    refine ⟨450219495541803341042677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38418730286233885102308437 450219495541803341042677)
                    ·
                      rfl

theorem cell22_1315199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_1315199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315199 prefixEnd_1315199 := by exact prefixLift 1315199
  have htrace : WordTrace (prefixWord ++ tailWord_1315199) baseStart_1315199 baseEnd_1315199 := by
    simpa [prefixWord, tailWord_1315199, baseEnd_1315199] using wordTrace_append hprefix tailTrace_1315199
  have hstable : (prefixWord ++ tailWord_1315199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315199).length < 2 ^ (prefixWord ++ tailWord_1315199).sum := by decide
  have hdescent : baseEnd_1315199 < baseStart_1315199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315278 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1315278 : Nat := 118140960795 + 1315278 * 2 ^ 59
def prefixEnd_1315278 : Nat := 4983230072969 + 3 ^ 40 * 1315278 * 2
def baseEnd_1315278 : Nat := 450246538856273468317435

theorem tailTrace_1315278 : CollatzResearch.WordTrace tailWord_1315278 prefixEnd_1315278 450246538856273468317435 := by
  unfold tailWord_1315278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996516216122489055459311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31981419819319941629116325 5996516216122489055459311)
  ·
    refine ⟨8994774324183733583188967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5996516216122489055459311 8994774324183733583188967)
    ·
      refine ⟨13492161486275600374783451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8994774324183733583188967 13492161486275600374783451)
      ·
        refine ⟨20238242229413400562175177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13492161486275600374783451 20238242229413400562175177)
        ·
          refine ⟨15178681672060050421631383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20238242229413400562175177 15178681672060050421631383)
          ·
            refine ⟨22768022508090075632447075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15178681672060050421631383 22768022508090075632447075)
            ·
              refine ⟨34152033762135113448670613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22768022508090075632447075 34152033762135113448670613)
              ·
                refine ⟨1600876582600083442906435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34152033762135113448670613 1600876582600083442906435)
                ·
                  refine ⟨2401314873900125164359653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600876582600083442906435 2401314873900125164359653)
                  ·
                    refine ⟨450246538856273468317435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401314873900125164359653 450246538856273468317435)
                    ·
                      rfl

theorem cell22_1315278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1315278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315278 prefixEnd_1315278 := by exact prefixLift 1315278
  have htrace : WordTrace (prefixWord ++ tailWord_1315278) baseStart_1315278 baseEnd_1315278 := by
    simpa [prefixWord, tailWord_1315278, baseEnd_1315278] using wordTrace_append hprefix tailTrace_1315278
  have hstable : (prefixWord ++ tailWord_1315278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315278).length < 2 ^ (prefixWord ++ tailWord_1315278).sum := by decide
  have hdescent : baseEnd_1315278 < baseStart_1315278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315295 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 1, 4]
def baseStart_1315295 : Nat := 118140960795 + 1315295 * 2 ^ 59
def prefixEnd_1315295 : Nat := 4983230072969 + 3 ^ 40 * 1315295 * 2
def baseEnd_1315295 : Nat := 450252358303691090642383

theorem tailTrace_1315295 : CollatzResearch.WordTrace tailWord_1315295 prefixEnd_1315295 450252358303691090642383 := by
  unfold tailWord_1315295
  simp only [CollatzResearch.WordTrace]
  refine ⟨47972749769918324347043339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31981833179945549564695559 47972749769918324347043339)
  ·
    refine ⟨71959124654877486520565009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47972749769918324347043339 71959124654877486520565009)
    ·
      refine ⟨53969343491158114890423757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71959124654877486520565009 53969343491158114890423757)
      ·
        refine ⟨20238503809184293083908909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53969343491158114890423757 20238503809184293083908909)
        ·
          refine ⟨7589438928444109906465841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20238503809184293083908909 7589438928444109906465841)
          ·
            refine ⟨5692079196333082429849381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7589438928444109906465841 5692079196333082429849381)
            ·
              refine ⟨1067264849312452955596759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5692079196333082429849381 1067264849312452955596759)
              ·
                refine ⟨1600897273968679433395139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067264849312452955596759 1600897273968679433395139)
                ·
                  refine ⟨2401345910953019150092709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600897273968679433395139 2401345910953019150092709)
                  ·
                    refine ⟨450252358303691090642383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401345910953019150092709 450252358303691090642383)
                    ·
                      rfl

theorem cell22_1315295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_1315295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315295 prefixEnd_1315295 := by exact prefixLift 1315295
  have htrace : WordTrace (prefixWord ++ tailWord_1315295) baseStart_1315295 baseEnd_1315295 := by
    simpa [prefixWord, tailWord_1315295, baseEnd_1315295] using wordTrace_append hprefix tailTrace_1315295
  have hstable : (prefixWord ++ tailWord_1315295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315295).length < 2 ^ (prefixWord ++ tailWord_1315295).sum := by decide
  have hdescent : baseEnd_1315295 < baseStart_1315295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315308 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_1315308 : Nat := 118140960795 + 1315308 * 2 ^ 59
def prefixEnd_1315308 : Nat := 4983230072969 + 3 ^ 40 * 1315308 * 2
def baseEnd_1315308 : Nat := 450256808469363390067343

theorem tailTrace_1315308 : CollatzResearch.WordTrace tailWord_1315308 prefixEnd_1315308 450256808469363390067343 := by
  unfold tailWord_1315308
  simp only [CollatzResearch.WordTrace]
  refine ⟨23986611959435613783633289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31982149279247485044844385 23986611959435613783633289)
  ·
    refine ⟨17989958969576710337724967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23986611959435613783633289 17989958969576710337724967)
    ·
      refine ⟨26984938454365065506587451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17989958969576710337724967 26984938454365065506587451)
      ·
        refine ⟨40477407681547598259881177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26984938454365065506587451 40477407681547598259881177)
        ·
          refine ⟨30358055761160698694910883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40477407681547598259881177 30358055761160698694910883)
          ·
            refine ⟨45537083641741048042366325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30358055761160698694910883 45537083641741048042366325)
            ·
              refine ⟨4269101591413223253971843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45537083641741048042366325 4269101591413223253971843)
              ·
                refine ⟨6403652387119834880957765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269101591413223253971843 6403652387119834880957765)
                ·
                  refine ⟨1200684822584969040179581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6403652387119834880957765 1200684822584969040179581)
                  ·
                    refine ⟨450256808469363390067343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200684822584969040179581 450256808469363390067343)
                    ·
                      rfl

theorem cell22_1315308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_1315308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315308 prefixEnd_1315308 := by exact prefixLift 1315308
  have htrace : WordTrace (prefixWord ++ tailWord_1315308) baseStart_1315308 baseEnd_1315308 := by
    simpa [prefixWord, tailWord_1315308, baseEnd_1315308] using wordTrace_append hprefix tailTrace_1315308
  have hstable : (prefixWord ++ tailWord_1315308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315308).length < 2 ^ (prefixWord ++ tailWord_1315308).sum := by decide
  have hdescent : baseEnd_1315308 < baseStart_1315308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315310 : List Nat := [4, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_1315310 : Nat := 118140960795 + 1315310 * 2 ^ 59
def prefixEnd_1315310 : Nat := 4983230072969 + 3 ^ 40 * 1315310 * 2
def baseEnd_1315310 : Nat := 150085831036745350505779

theorem tailTrace_1315310 : CollatzResearch.WordTrace tailWord_1315310 prefixEnd_1315310 150085831036745350505779 := by
  unfold tailWord_1315310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996662108107997738604923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31982197909909321272559589 5996662108107997738604923)
  ·
    refine ⟨8994993162161996607907385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5996662108107997738604923 8994993162161996607907385)
    ·
      refine ⟨6746244871621497455930539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8994993162161996607907385 6746244871621497455930539)
      ·
        refine ⟨10119367307432246183895809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6746244871621497455930539 10119367307432246183895809)
        ·
          refine ⟨7589525480574184637921857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10119367307432246183895809 7589525480574184637921857)
          ·
            refine ⟨5692144110430638478441393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7589525480574184637921857 5692144110430638478441393)
            ·
              refine ⟨4269108082822978858831045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5692144110430638478441393 4269108082822978858831045)
              ·
                refine ⟨800457765529308536030821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4269108082822978858831045 800457765529308536030821)
                ·
                  refine ⟨150085831036745350505779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 800457765529308536030821 150085831036745350505779)
                  ·
                    rfl

theorem cell22_1315310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_1315310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315310 prefixEnd_1315310 := by exact prefixLift 1315310
  have htrace : WordTrace (prefixWord ++ tailWord_1315310) baseStart_1315310 baseEnd_1315310 := by
    simpa [prefixWord, tailWord_1315310, baseEnd_1315310] using wordTrace_append hprefix tailTrace_1315310
  have hstable : (prefixWord ++ tailWord_1315310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315310).length < 2 ^ (prefixWord ++ tailWord_1315310).sum := by decide
  have hdescent : baseEnd_1315310 < baseStart_1315310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315336 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_1315336 : Nat := 118140960795 + 1315336 * 2 ^ 59
def prefixEnd_1315336 : Nat := 4983230072969 + 3 ^ 40 * 1315336 * 2
def baseEnd_1315336 : Nat := 450266393441580650367257

theorem tailTrace_1315336 : CollatzResearch.WordTrace tailWord_1315336 prefixEnd_1315336 450266393441580650367257 := by
  unfold tailWord_1315336
  simp only [CollatzResearch.WordTrace]
  refine ⟨23987122581384894174642931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31982830108513192232857241 23987122581384894174642931)
  ·
    refine ⟨35980683872077341261964397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23987122581384894174642931 35980683872077341261964397)
    ·
      refine ⟨13492756452029002973236649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35980683872077341261964397 13492756452029002973236649)
      ·
        refine ⟨10119567339021752229927487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13492756452029002973236649 10119567339021752229927487)
        ·
          refine ⟨15179351008532628344891231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10119567339021752229927487 15179351008532628344891231)
          ·
            refine ⟨22769026512798942517336847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15179351008532628344891231 22769026512798942517336847)
            ·
              refine ⟨34153539769198413776005271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22769026512798942517336847 34153539769198413776005271)
              ·
                refine ⟨51230309653797620664007907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34153539769198413776005271 51230309653797620664007907)
                ·
                  refine ⟨76845464480696430996011861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51230309653797620664007907 76845464480696430996011861)
                  ·
                    refine ⟨450266393441580650367257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 76845464480696430996011861 450266393441580650367257)
                    ·
                      rfl

theorem cell22_1315336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1315336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315336 prefixEnd_1315336 := by exact prefixLift 1315336
  have htrace : WordTrace (prefixWord ++ tailWord_1315336) baseStart_1315336 baseEnd_1315336 := by
    simpa [prefixWord, tailWord_1315336, baseEnd_1315336] using wordTrace_append hprefix tailTrace_1315336
  have hstable : (prefixWord ++ tailWord_1315336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315336).length < 2 ^ (prefixWord ++ tailWord_1315336).sum := by decide
  have hdescent : baseEnd_1315336 < baseStart_1315336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315383 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 5]
def baseStart_1315383 : Nat := 118140960795 + 1315383 * 2 ^ 59
def prefixEnd_1315383 : Nat := 4983230072969 + 3 ^ 40 * 1315383 * 2
def baseEnd_1315383 : Nat := 150094160834029398147371

theorem tailTrace_1315383 : CollatzResearch.WordTrace tailWord_1315383 prefixEnd_1315383 150094160834029398147371 := by
  unfold tailWord_1315383
  simp only [CollatzResearch.WordTrace]
  refine ⟨47975959393599515376246803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31983972929066343584164535 47975959393599515376246803)
  ·
    refine ⟨71963939090399273064370205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47975959393599515376246803 71963939090399273064370205)
    ·
      refine ⟨26986477158899727399138827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71963939090399273064370205 26986477158899727399138827)
      ·
        refine ⟨40479715738349591098708241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26986477158899727399138827 40479715738349591098708241)
        ·
          refine ⟨30359786803762193324031181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40479715738349591098708241 30359786803762193324031181)
          ·
            refine ⟨11384920051410822496511693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30359786803762193324031181 11384920051410822496511693)
            ·
              refine ⟨4269345019279058436191885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11384920051410822496511693 4269345019279058436191885)
              ·
                refine ⟨1601004382229646913571957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4269345019279058436191885 1601004382229646913571957)
                ·
                  refine ⟨150094160834029398147371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1601004382229646913571957 150094160834029398147371)
                  ·
                    rfl

theorem cell22_1315383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 5].length) (baseStart_1315383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315383 prefixEnd_1315383 := by exact prefixLift 1315383
  have htrace : WordTrace (prefixWord ++ tailWord_1315383) baseStart_1315383 baseEnd_1315383 := by
    simpa [prefixWord, tailWord_1315383, baseEnd_1315383] using wordTrace_append hprefix tailTrace_1315383
  have hstable : (prefixWord ++ tailWord_1315383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315383).length < 2 ^ (prefixWord ++ tailWord_1315383).sum := by decide
  have hdescent : baseEnd_1315383 < baseStart_1315383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315428 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 6]
def baseStart_1315428 : Nat := 118140960795 + 1315428 * 2 ^ 59
def prefixEnd_1315428 : Nat := 4983230072969 + 3 ^ 40 * 1315428 * 2
def baseEnd_1315428 : Nat := 150099295640574359022325

theorem tailTrace_1315428 : CollatzResearch.WordTrace tailWord_1315428 prefixEnd_1315428 150099295640574359022325 := by
  unfold tailWord_1315428
  simp only [CollatzResearch.WordTrace]
  refine ⟨23988800339218244030817469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31985067118957658707756625 23988800339218244030817469)
  ·
    refine ⟨8995800127206841511556551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23988800339218244030817469 8995800127206841511556551)
    ·
      refine ⟨13493700190810262267334827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8995800127206841511556551 13493700190810262267334827)
      ·
        refine ⟨20240550286215393401002241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13493700190810262267334827 20240550286215393401002241)
        ·
          refine ⟨15180412714661545050751681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20240550286215393401002241 15180412714661545050751681)
          ·
            refine ⟨11385309535996158788063761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15180412714661545050751681 11385309535996158788063761)
            ·
              refine ⟨8538982151997119091047821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11385309535996158788063761 8538982151997119091047821)
              ·
                refine ⟨3202118306998919659142933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8538982151997119091047821 3202118306998919659142933)
                ·
                  refine ⟨150099295640574359022325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3202118306998919659142933 150099295640574359022325)
                  ·
                    rfl

theorem cell22_1315428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_1315428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315428 prefixEnd_1315428 := by exact prefixLift 1315428
  have htrace : WordTrace (prefixWord ++ tailWord_1315428) baseStart_1315428 baseEnd_1315428 := by
    simpa [prefixWord, tailWord_1315428, baseEnd_1315428] using wordTrace_append hprefix tailTrace_1315428
  have hstable : (prefixWord ++ tailWord_1315428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315428).length < 2 ^ (prefixWord ++ tailWord_1315428).sum := by decide
  have hdescent : baseEnd_1315428 < baseStart_1315428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315460 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1315460 : Nat := 118140960795 + 1315460 * 2 ^ 59
def prefixEnd_1315460 : Nat := 4983230072969 + 3 ^ 40 * 1315460 * 2
def baseEnd_1315460 : Nat := 450308841175685660266877

theorem tailTrace_1315460 : CollatzResearch.WordTrace tailWord_1315460 prefixEnd_1315460 450308841175685660266877 := by
  unfold tailWord_1315460
  simp only [CollatzResearch.WordTrace]
  refine ⟨23989383907160278763399917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31985845209547038351199889 23989383907160278763399917)
  ·
    refine ⟨8996018965185104536274969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23989383907160278763399917 8996018965185104536274969)
    ·
      refine ⟨6747014223888828402206227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8996018965185104536274969 6747014223888828402206227)
      ·
        refine ⟨10120521335833242603309341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6747014223888828402206227 10120521335833242603309341)
        ·
          refine ⟨3795195500937465976241003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10120521335833242603309341 3795195500937465976241003)
          ·
            refine ⟨5692793251406198964361505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795195500937465976241003 5692793251406198964361505)
            ·
              refine ⟨4269594938554649223271129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5692793251406198964361505 4269594938554649223271129)
              ·
                refine ⟨3202196203915986917453347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269594938554649223271129 3202196203915986917453347)
                ·
                  refine ⟨4803294305873980376180021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202196203915986917453347 4803294305873980376180021)
                  ·
                    refine ⟨450308841175685660266877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4803294305873980376180021 450308841175685660266877)
                    ·
                      rfl

theorem cell22_1315460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1315460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315460 prefixEnd_1315460 := by exact prefixLift 1315460
  have htrace : WordTrace (prefixWord ++ tailWord_1315460) baseStart_1315460 baseEnd_1315460 := by
    simpa [prefixWord, tailWord_1315460, baseEnd_1315460] using wordTrace_append hprefix tailTrace_1315460
  have hstable : (prefixWord ++ tailWord_1315460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315460).length < 2 ^ (prefixWord ++ tailWord_1315460).sum := by decide
  have hdescent : baseEnd_1315460 < baseStart_1315460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315526 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1315526 : Nat := 118140960795 + 1315526 * 2 ^ 59
def prefixEnd_1315526 : Nat := 4983230072969 + 3 ^ 40 * 1315526 * 2
def baseEnd_1315526 : Nat := 450331434324483488116675

theorem tailTrace_1315526 : CollatzResearch.WordTrace tailWord_1315526 prefixEnd_1315526 450331434324483488116675 := by
  unfold tailWord_1315526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499411719752545337459451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31987450021387633865801621 1499411719752545337459451)
  ·
    refine ⟨2249117579628818006189177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1499411719752545337459451 2249117579628818006189177)
    ·
      refine ⟨1686838184721613504641883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2249117579628818006189177 1686838184721613504641883)
      ·
        refine ⟨2530257277082420256962825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686838184721613504641883 2530257277082420256962825)
        ·
          refine ⟨1897692957811815192722119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2530257277082420256962825 1897692957811815192722119)
          ·
            refine ⟨2846539436717722789083179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897692957811815192722119 2846539436717722789083179)
            ·
              refine ⟨4269809155076584183624769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846539436717722789083179 4269809155076584183624769)
              ·
                refine ⟨3202356866307438137718577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269809155076584183624769 3202356866307438137718577)
                ·
                  refine ⟨2401767649730578603288933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3202356866307438137718577 2401767649730578603288933)
                  ·
                    refine ⟨450331434324483488116675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401767649730578603288933 450331434324483488116675)
                    ·
                      rfl

theorem cell22_1315526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1315526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315526 prefixEnd_1315526 := by exact prefixLift 1315526
  have htrace : WordTrace (prefixWord ++ tailWord_1315526) baseStart_1315526 baseEnd_1315526 := by
    simpa [prefixWord, tailWord_1315526, baseEnd_1315526] using wordTrace_append hprefix tailTrace_1315526
  have hstable : (prefixWord ++ tailWord_1315526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315526).length < 2 ^ (prefixWord ++ tailWord_1315526).sum := by decide
  have hdescent : baseEnd_1315526 < baseStart_1315526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315563 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 8]
def baseStart_1315563 : Nat := 118140960795 + 1315563 * 2 ^ 59
def prefixEnd_1315563 : Nat := 4983230072969 + 3 ^ 40 * 1315563 * 2
def baseEnd_1315563 : Nat := 150114700060209241647187

theorem tailTrace_1315563 : CollatzResearch.WordTrace tailWord_1315563 prefixEnd_1315563 150114700060209241647187 := by
  unfold tailWord_1315563
  simp only [CollatzResearch.WordTrace]
  refine ⟨47982524532947406117799343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31988349688631604078532895 47982524532947406117799343)
  ·
    refine ⟨71973786799421109176699015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47982524532947406117799343 71973786799421109176699015)
    ·
      refine ⟨107960680199131663765048523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71973786799421109176699015 107960680199131663765048523)
      ·
        refine ⟨161941020298697495647572785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107960680199131663765048523 161941020298697495647572785)
        ·
          refine ⟨121455765224023121735679589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161941020298697495647572785 121455765224023121735679589)
          ·
            refine ⟨22772955979504335325439923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121455765224023121735679589 22772955979504335325439923)
            ·
              refine ⟨34159433969256502988159885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22772955979504335325439923 34159433969256502988159885)
              ·
                refine ⟨12809787738471188620559957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34159433969256502988159885 12809787738471188620559957)
                ·
                  refine ⟨150114700060209241647187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12809787738471188620559957 150114700060209241647187)
                  ·
                    rfl

theorem cell22_1315563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_1315563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315563 prefixEnd_1315563 := by exact prefixLift 1315563
  have htrace : WordTrace (prefixWord ++ tailWord_1315563) baseStart_1315563 baseEnd_1315563 := by
    simpa [prefixWord, tailWord_1315563, baseEnd_1315563] using wordTrace_append hprefix tailTrace_1315563
  have hstable : (prefixWord ++ tailWord_1315563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315563).length < 2 ^ (prefixWord ++ tailWord_1315563).sum := by decide
  have hdescent : baseEnd_1315563 < baseStart_1315563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315610 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_1315610 : Nat := 118140960795 + 1315610 * 2 ^ 59
def prefixEnd_1315610 : Nat := 4983230072969 + 3 ^ 40 * 1315610 * 2
def baseEnd_1315610 : Nat := 450360189241135269016417

theorem tailTrace_1315610 : CollatzResearch.WordTrace tailWord_1315610 prefixEnd_1315610 450360189241135269016417 := by
  unfold tailWord_1315610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996059690944283286190071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31989492509184755429840189 11996059690944283286190071)
  ·
    refine ⟨17994089536416424929285107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11996059690944283286190071 17994089536416424929285107)
    ·
      refine ⟨26991134304624637393927661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17994089536416424929285107 26991134304624637393927661)
      ·
        refine ⟨10121675364234239022722873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26991134304624637393927661 10121675364234239022722873)
        ·
          refine ⟨7591256523175679267042155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10121675364234239022722873 7591256523175679267042155)
          ·
            refine ⟨11386884784763518900563233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7591256523175679267042155 11386884784763518900563233)
            ·
              refine ⟨8540163588572639175422425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11386884784763518900563233 8540163588572639175422425)
              ·
                refine ⟨6405122691429479381566819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8540163588572639175422425 6405122691429479381566819)
                ·
                  refine ⟨9607684037144219072350229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6405122691429479381566819 9607684037144219072350229)
                  ·
                    refine ⟨450360189241135269016417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9607684037144219072350229 450360189241135269016417)
                    ·
                      rfl

theorem cell22_1315610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_1315610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315610 prefixEnd_1315610 := by exact prefixLift 1315610
  have htrace : WordTrace (prefixWord ++ tailWord_1315610) baseStart_1315610 baseEnd_1315610 := by
    simpa [prefixWord, tailWord_1315610, baseEnd_1315610] using wordTrace_append hprefix tailTrace_1315610
  have hstable : (prefixWord ++ tailWord_1315610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315610).length < 2 ^ (prefixWord ++ tailWord_1315610).sum := by decide
  have hdescent : baseEnd_1315610 < baseStart_1315610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315612 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1315612 : Nat := 118140960795 + 1315612 * 2 ^ 59
def prefixEnd_1315612 : Nat := 4983230072969 + 3 ^ 40 * 1315612 * 2
def baseEnd_1315612 : Nat := 450360873882007930466411

theorem tailTrace_1315612 : CollatzResearch.WordTrace tailWord_1315612 prefixEnd_1315612 450360873882007930466411 := by
  unfold tailWord_1315612
  simp only [CollatzResearch.WordTrace]
  refine ⟨23992155854884943743166545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31989541139846591657555393 23992155854884943743166545)
  ·
    refine ⟨17994116891163707807374909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23992155854884943743166545 17994116891163707807374909)
    ·
      refine ⟨6747793834186390427765591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17994116891163707807374909 6747793834186390427765591)
      ·
        refine ⟨10121690751279585641648387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6747793834186390427765591 10121690751279585641648387)
        ·
          refine ⟨15182536126919378462472581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10121690751279585641648387 15182536126919378462472581)
          ·
            refine ⟨2846725523797383461713609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15182536126919378462472581 2846725523797383461713609)
            ·
              refine ⟨2135044142848037596285207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2846725523797383461713609 2135044142848037596285207)
              ·
                refine ⟨3202566214272056394427811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2135044142848037596285207 3202566214272056394427811)
                ·
                  refine ⟨4803849321408084591641717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202566214272056394427811 4803849321408084591641717)
                  ·
                    refine ⟨450360873882007930466411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4803849321408084591641717 450360873882007930466411)
                    ·
                      rfl

theorem cell22_1315612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1315612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315612 prefixEnd_1315612 := by exact prefixLift 1315612
  have htrace : WordTrace (prefixWord ++ tailWord_1315612) baseStart_1315612 baseEnd_1315612 := by
    simpa [prefixWord, tailWord_1315612, baseEnd_1315612] using wordTrace_append hprefix tailTrace_1315612
  have hstable : (prefixWord ++ tailWord_1315612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315612).length < 2 ^ (prefixWord ++ tailWord_1315612).sum := by decide
  have hdescent : baseEnd_1315612 < baseStart_1315612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315657 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 3, 3]
def baseStart_1315657 : Nat := 118140960795 + 1315657 * 2 ^ 59
def prefixEnd_1315657 : Nat := 4983230072969 + 3 ^ 40 * 1315657 * 2
def baseEnd_1315657 : Nat := 450376278301642813091273

theorem tailTrace_1315657 : CollatzResearch.WordTrace tailWord_1315657 prefixEnd_1315657 450376278301642813091273 := by
  unfold tailWord_1315657
  simp only [CollatzResearch.WordTrace]
  refine ⟨47985952994606860171721225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31990635329737906781147483 47985952994606860171721225)
  ·
    refine ⟨35989464745955145128790919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47985952994606860171721225 35989464745955145128790919)
    ·
      refine ⟨53984197118932717693186379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35989464745955145128790919 53984197118932717693186379)
      ·
        refine ⟨80976295678399076539779569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53984197118932717693186379 80976295678399076539779569)
        ·
          refine ⟨60732221758799307404834677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80976295678399076539779569 60732221758799307404834677)
          ·
            refine ⟨5693645789887435069203251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60732221758799307404834677 5693645789887435069203251)
            ·
              refine ⟨8540468684831152603804877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693645789887435069203251 8540468684831152603804877)
              ·
                refine ⟨3202675756811682226426829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8540468684831152603804877 3202675756811682226426829)
                ·
                  refine ⟨1201003408804380834910061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3202675756811682226426829 1201003408804380834910061)
                  ·
                    refine ⟨450376278301642813091273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1201003408804380834910061 450376278301642813091273)
                    ·
                      rfl

theorem cell22_1315657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_1315657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315657 prefixEnd_1315657 := by exact prefixLift 1315657
  have htrace : WordTrace (prefixWord ++ tailWord_1315657) baseStart_1315657 baseEnd_1315657 := by
    simpa [prefixWord, tailWord_1315657, baseEnd_1315657] using wordTrace_append hprefix tailTrace_1315657
  have hstable : (prefixWord ++ tailWord_1315657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315657).length < 2 ^ (prefixWord ++ tailWord_1315657).sum := by decide
  have hdescent : baseEnd_1315657 < baseStart_1315657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315685 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_1315685 : Nat := 118140960795 + 1315685 * 2 ^ 59
def prefixEnd_1315685 : Nat := 4983230072969 + 3 ^ 40 * 1315685 * 2
def baseEnd_1315685 : Nat := 450385863273860073391187

theorem tailTrace_1315685 : CollatzResearch.WordTrace tailWord_1315685 prefixEnd_1315685 450385863273860073391187 := by
  unfold tailWord_1315685
  simp only [CollatzResearch.WordTrace]
  refine ⟨47986974238505420953740509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31991316159003613969160339 47986974238505420953740509)
  ·
    refine ⟨17995115339439532857652691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47986974238505420953740509 17995115339439532857652691)
    ·
      refine ⟨26992673009159299286479037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17995115339439532857652691 26992673009159299286479037)
      ·
        refine ⟨10122252378434737232429639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26992673009159299286479037 10122252378434737232429639)
        ·
          refine ⟨15183378567652105848644459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10122252378434737232429639 15183378567652105848644459)
          ·
            refine ⟨22775067851478158772966689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15183378567652105848644459 22775067851478158772966689)
            ·
              refine ⟨17081300888608619079725017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22775067851478158772966689 17081300888608619079725017)
              ·
                refine ⟨12810975666456464309793763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17081300888608619079725017 12810975666456464309793763)
                ·
                  refine ⟨19216463499684696464690645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12810975666456464309793763 19216463499684696464690645)
                  ·
                    refine ⟨450385863273860073391187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19216463499684696464690645 450385863273860073391187)
                    ·
                      rfl

theorem cell22_1315685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_1315685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315685 prefixEnd_1315685 := by exact prefixLift 1315685
  have htrace : WordTrace (prefixWord ++ tailWord_1315685) baseStart_1315685 baseEnd_1315685 := by
    simpa [prefixWord, tailWord_1315685, baseEnd_1315685] using wordTrace_append hprefix tailTrace_1315685
  have hstable : (prefixWord ++ tailWord_1315685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315685).length < 2 ^ (prefixWord ++ tailWord_1315685).sum := by decide
  have hdescent : baseEnd_1315685 < baseStart_1315685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315732 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1315732 : Nat := 118140960795 + 1315732 * 2 ^ 59
def prefixEnd_1315732 : Nat := 4983230072969 + 3 ^ 40 * 1315732 * 2
def baseEnd_1315732 : Nat := 150133984111455872488681

theorem tailTrace_1315732 : CollatzResearch.WordTrace tailWord_1315732 prefixEnd_1315732 150133984111455872488681 := by
  unfold tailWord_1315732
  simp only [CollatzResearch.WordTrace]
  refine ⟨23994344234667573990350725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31992458979556765320467633 23994344234667573990350725)
  ·
    refine ⟨4498939544000170123190761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23994344234667573990350725 4498939544000170123190761)
    ·
      refine ⟨3374204658000127592393071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4498939544000170123190761 3374204658000127592393071)
      ·
        refine ⟨5061306987000191388589607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374204658000127592393071 5061306987000191388589607)
        ·
          refine ⟨7591960480500287082884411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061306987000191388589607 7591960480500287082884411)
          ·
            refine ⟨11387940720750430624326617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7591960480500287082884411 11387940720750430624326617)
            ·
              refine ⟨8540955540562822968244963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11387940720750430624326617 8540955540562822968244963)
              ·
                refine ⟨12811433310844234452367445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8540955540562822968244963 12811433310844234452367445)
                ·
                  refine ⟨150133984111455872488681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12811433310844234452367445 150133984111455872488681)
                  ·
                    rfl

theorem cell22_1315732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1315732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315732 prefixEnd_1315732 := by exact prefixLift 1315732
  have htrace : WordTrace (prefixWord ++ tailWord_1315732) baseStart_1315732 baseEnd_1315732 := by
    simpa [prefixWord, tailWord_1315732, baseEnd_1315732] using wordTrace_append hprefix tailTrace_1315732
  have hstable : (prefixWord ++ tailWord_1315732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315732).length < 2 ^ (prefixWord ++ tailWord_1315732).sum := by decide
  have hdescent : baseEnd_1315732 < baseStart_1315732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315747 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 6, 3]
def baseStart_1315747 : Nat := 118140960795 + 1315747 * 2 ^ 59
def prefixEnd_1315747 : Nat := 4983230072969 + 3 ^ 40 * 1315747 * 2
def baseEnd_1315747 : Nat := 450407087140912578340997

theorem tailTrace_1315747 : CollatzResearch.WordTrace tailWord_1315747 prefixEnd_1315747 450407087140912578340997 := by
  unfold tailWord_1315747
  simp only [CollatzResearch.WordTrace]
  refine ⟨47989235564280805542497495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31992823709520537028331663 47989235564280805542497495)
  ·
    refine ⟨71983853346421208313746243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47989235564280805542497495 71983853346421208313746243)
    ·
      refine ⟨107975780019631812470619365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71983853346421208313746243 107975780019631812470619365)
      ·
        refine ⟨20245458753680964838241131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107975780019631812470619365 20245458753680964838241131)
        ·
          refine ⟨30368188130521447257361697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20245458753680964838241131 30368188130521447257361697)
          ·
            refine ⟨22776141097891085443021273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30368188130521447257361697 22776141097891085443021273)
            ·
              refine ⟨17082105823418314082265955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22776141097891085443021273 17082105823418314082265955)
              ·
                refine ⟨25623158735127471123398933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17082105823418314082265955 25623158735127471123398933)
                ·
                  refine ⟨1201085565709100208909325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25623158735127471123398933 1201085565709100208909325)
                  ·
                    refine ⟨450407087140912578340997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1201085565709100208909325 450407087140912578340997)
                    ·
                      rfl

theorem cell22_1315747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 3].length) (baseStart_1315747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315747 prefixEnd_1315747 := by exact prefixLift 1315747
  have htrace : WordTrace (prefixWord ++ tailWord_1315747) baseStart_1315747 baseEnd_1315747 := by
    simpa [prefixWord, tailWord_1315747, baseEnd_1315747] using wordTrace_append hprefix tailTrace_1315747
  have hstable : (prefixWord ++ tailWord_1315747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315747).length < 2 ^ (prefixWord ++ tailWord_1315747).sum := by decide
  have hdescent : baseEnd_1315747 < baseStart_1315747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315796 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1315796 : Nat := 118140960795 + 1315796 * 2 ^ 59
def prefixEnd_1315796 : Nat := 4983230072969 + 3 ^ 40 * 1315796 * 2
def baseEnd_1315796 : Nat := 450423860842292783865847

theorem tailTrace_1315796 : CollatzResearch.WordTrace tailWord_1315796 prefixEnd_1315796 450423860842292783865847 := by
  unfold tailWord_1315796
  simp only [CollatzResearch.WordTrace]
  refine ⟨23995511370551643455515621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31994015160735524607354161 23995511370551643455515621)
  ·
    refine ⟨4499158381978433147909179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23995511370551643455515621 4499158381978433147909179)
    ·
      refine ⟨6748737572967649721863769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499158381978433147909179 6748737572967649721863769)
      ·
        refine ⟨5061553179725737291397827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748737572967649721863769 5061553179725737291397827)
        ·
          refine ⟨7592329769588605937096741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061553179725737291397827 7592329769588605937096741)
          ·
            refine ⟨1423561831797863613205639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7592329769588605937096741 1423561831797863613205639)
            ·
              refine ⟨2135342747696795419808459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423561831797863613205639 2135342747696795419808459)
              ·
                refine ⟨3203014121545193129712689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2135342747696795419808459 3203014121545193129712689)
                ·
                  refine ⟨2402260591158894847284517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203014121545193129712689 2402260591158894847284517)
                  ·
                    refine ⟨450423860842292783865847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2402260591158894847284517 450423860842292783865847)
                    ·
                      rfl

theorem cell22_1315796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1315796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315796 prefixEnd_1315796 := by exact prefixLift 1315796
  have htrace : WordTrace (prefixWord ++ tailWord_1315796) baseStart_1315796 baseEnd_1315796 := by
    simpa [prefixWord, tailWord_1315796, baseEnd_1315796] using wordTrace_append hprefix tailTrace_1315796
  have hstable : (prefixWord ++ tailWord_1315796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315796).length < 2 ^ (prefixWord ++ tailWord_1315796).sum := by decide
  have hdescent : baseEnd_1315796 < baseStart_1315796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315912 : List Nat := [2, 1, 3, 1, 1, 1, 3, 10]
def baseStart_1315912 : Nat := 118140960795 + 1315912 * 2 ^ 59
def prefixEnd_1315912 : Nat := 4983230072969 + 3 ^ 40 * 1315912 * 2
def baseEnd_1315912 : Nat := 50051507779211905329499

theorem tailTrace_1315912 : CollatzResearch.WordTrace tailWord_1315912 prefixEnd_1315912 50051507779211905329499 := by
  unfold tailWord_1315912
  simp only [CollatzResearch.WordTrace]
  refine ⟨23997626804341519361126995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31996835739122025814835993 23997626804341519361126995)
  ·
    refine ⟨35996440206512279041690493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23997626804341519361126995 35996440206512279041690493)
    ·
      refine ⟨13498665077442104640633935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35996440206512279041690493 13498665077442104640633935)
      ·
        refine ⟨20247997616163156960950903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13498665077442104640633935 20247997616163156960950903)
        ·
          refine ⟨30371996424244735441426355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20247997616163156960950903 30371996424244735441426355)
          ·
            refine ⟨45557994636367103162139533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30371996424244735441426355 45557994636367103162139533)
            ·
              refine ⟨17084247988637663685802325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45557994636367103162139533 17084247988637663685802325)
              ·
                refine ⟨50051507779211905329499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17084247988637663685802325 50051507779211905329499)
                ·
                  rfl

theorem cell22_1315912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_1315912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315912 prefixEnd_1315912 := by exact prefixLift 1315912
  have htrace : WordTrace (prefixWord ++ tailWord_1315912) baseStart_1315912 baseEnd_1315912 := by
    simpa [prefixWord, tailWord_1315912, baseEnd_1315912] using wordTrace_append hprefix tailTrace_1315912
  have hstable : (prefixWord ++ tailWord_1315912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315912).length < 2 ^ (prefixWord ++ tailWord_1315912).sum := by decide
  have hdescent : baseEnd_1315912 < baseStart_1315912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315914 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1315914 : Nat := 118140960795 + 1315914 * 2 ^ 59
def prefixEnd_1315914 : Nat := 4983230072969 + 3 ^ 40 * 1315914 * 2
def baseEnd_1315914 : Nat := 450464254653779809415485

theorem tailTrace_1315914 : CollatzResearch.WordTrace tailWord_1315914 prefixEnd_1315914 450464254653779809415485 := by
  unfold tailWord_1315914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998831638668948265956699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31996884369783862042551197 11998831638668948265956699)
  ·
    refine ⟨17998247458003422398935049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11998831638668948265956699 17998247458003422398935049)
    ·
      refine ⟨13498685593502566799201287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17998247458003422398935049 13498685593502566799201287)
      ·
        refine ⟨20248028390253850198801931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13498685593502566799201287 20248028390253850198801931)
        ·
          refine ⟨30372042585380775298202897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20248028390253850198801931 30372042585380775298202897)
          ·
            refine ⟨22779031939035581473652173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30372042585380775298202897 22779031939035581473652173)
            ·
              refine ⟨8542136977138343052619565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22779031939035581473652173 8542136977138343052619565)
              ·
                refine ⟨3203301366426878644732337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8542136977138343052619565 3203301366426878644732337)
                ·
                  refine ⟨2402476024820158983549253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203301366426878644732337 2402476024820158983549253)
                  ·
                    refine ⟨450464254653779809415485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2402476024820158983549253 450464254653779809415485)
                    ·
                      rfl

theorem cell22_1315914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1315914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315914 prefixEnd_1315914 := by exact prefixLift 1315914
  have htrace : WordTrace (prefixWord ++ tailWord_1315914) baseStart_1315914 baseEnd_1315914 := by
    simpa [prefixWord, tailWord_1315914, baseEnd_1315914] using wordTrace_append hprefix tailTrace_1315914
  have hstable : (prefixWord ++ tailWord_1315914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315914).length < 2 ^ (prefixWord ++ tailWord_1315914).sum := by decide
  have hdescent : baseEnd_1315914 < baseStart_1315914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315946 : List Nat := [3, 1, 3, 2, 2, 3, 1, 7]
def baseStart_1315946 : Nat := 118140960795 + 1315946 * 2 ^ 59
def prefixEnd_1315946 : Nat := 4983230072969 + 3 ^ 40 * 1315946 * 2
def baseEnd_1315946 : Nat := 50052800989749154735043

theorem tailTrace_1315946 : CollatzResearch.WordTrace tailWord_1315946 prefixEnd_1315946 50052800989749154735043 := by
  unfold tailWord_1315946
  simp only [CollatzResearch.WordTrace]
  refine ⟨11999123422639965632247923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31997662460373241685994461 11999123422639965632247923)
  ·
    refine ⟨17998685133959948448371885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11999123422639965632247923 17998685133959948448371885)
    ·
      refine ⟨6749506925234980668139457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17998685133959948448371885 6749506925234980668139457)
      ·
        refine ⟨5062130193926235501104593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6749506925234980668139457 5062130193926235501104593)
        ·
          refine ⟨3796597645444676625828445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5062130193926235501104593 3796597645444676625828445)
          ·
            refine ⟨1423724117041753734685667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3796597645444676625828445 1423724117041753734685667)
            ·
              refine ⟨2135586175562630602028501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423724117041753734685667 2135586175562630602028501)
              ·
                refine ⟨50052800989749154735043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2135586175562630602028501 50052800989749154735043)
                ·
                  rfl

theorem cell22_1315946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_1315946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315946 prefixEnd_1315946 := by exact prefixLift 1315946
  have htrace : WordTrace (prefixWord ++ tailWord_1315946) baseStart_1315946 baseEnd_1315946 := by
    simpa [prefixWord, tailWord_1315946, baseEnd_1315946] using wordTrace_append hprefix tailTrace_1315946
  have hstable : (prefixWord ++ tailWord_1315946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315946).length < 2 ^ (prefixWord ++ tailWord_1315946).sum := by decide
  have hdescent : baseEnd_1315946 < baseStart_1315946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315991 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 5]
def baseStart_1315991 : Nat := 118140960795 + 1315991 * 2 ^ 59
def prefixEnd_1315991 : Nat := 4983230072969 + 3 ^ 40 * 1315991 * 2
def baseEnd_1315991 : Nat := 150163537775792425080083

theorem tailTrace_1315991 : CollatzResearch.WordTrace tailWord_1315991 prefixEnd_1315991 150163537775792425080083 := by
  unfold tailWord_1315991
  simp only [CollatzResearch.WordTrace]
  refine ⟨47998134975396835214379827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31998756650264556809586551 47998134975396835214379827)
  ·
    refine ⟨71997202463095252821569741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47998134975396835214379827 71997202463095252821569741)
    ·
      refine ⟨26998950923660719808088653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71997202463095252821569741 26998950923660719808088653)
      ·
        refine ⟨10124606596372769928033245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26998950923660719808088653 10124606596372769928033245)
        ·
          refine ⟨3796727473639788723012467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10124606596372769928033245 3796727473639788723012467)
          ·
            refine ⟨5695091210459683084518701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796727473639788723012467 5695091210459683084518701)
            ·
              refine ⟨2135659203922381156694513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5695091210459683084518701 2135659203922381156694513)
              ·
                refine ⟨1601744402941785867520885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135659203922381156694513 1601744402941785867520885)
                ·
                  refine ⟨150163537775792425080083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1601744402941785867520885 150163537775792425080083)
                  ·
                    rfl

theorem cell22_1315991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 5].length) (baseStart_1315991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1315991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1315991 prefixEnd_1315991 := by exact prefixLift 1315991
  have htrace : WordTrace (prefixWord ++ tailWord_1315991) baseStart_1315991 baseEnd_1315991 := by
    simpa [prefixWord, tailWord_1315991, baseEnd_1315991] using wordTrace_append hprefix tailTrace_1315991
  have hstable : (prefixWord ++ tailWord_1315991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315991).length < 2 ^ (prefixWord ++ tailWord_1315991).sum := by decide
  have hdescent : baseEnd_1315991 < baseStart_1315991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316019 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 6]
def baseStart_1316019 : Nat := 118140960795 + 1316019 * 2 ^ 59
def prefixEnd_1316019 : Nat := 4983230072969 + 3 ^ 40 * 1316019 * 2
def baseEnd_1316019 : Nat := 150166732766531511846721

theorem tailTrace_1316019 : CollatzResearch.WordTrace tailWord_1316019 prefixEnd_1316019 150166732766531511846721 := by
  unfold tailWord_1316019
  simp only [CollatzResearch.WordTrace]
  refine ⟨47999156219295395996399111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31999437479530263997599407 47999156219295395996399111)
  ·
    refine ⟨71998734328943093994598667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47999156219295395996399111 71998734328943093994598667)
    ·
      refine ⟨107998101493414640991898001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71998734328943093994598667 107998101493414640991898001)
      ·
        refine ⟨80998576120060980743923501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107998101493414640991898001 80998576120060980743923501)
        ·
          refine ⟨30374466045022867778971313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80998576120060980743923501 30374466045022867778971313)
          ·
            refine ⟨22780849533767150834228485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30374466045022867778971313 22780849533767150834228485)
            ·
              refine ⟨4271409287581340781417841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22780849533767150834228485 4271409287581340781417841)
              ·
                refine ⟨3203556965686005586063381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4271409287581340781417841 3203556965686005586063381)
                ·
                  refine ⟨150166732766531511846721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3203556965686005586063381 150166732766531511846721)
                  ·
                    rfl

theorem cell22_1316019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 6].length) (baseStart_1316019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316019 prefixEnd_1316019 := by exact prefixLift 1316019
  have htrace : WordTrace (prefixWord ++ tailWord_1316019) baseStart_1316019 baseEnd_1316019 := by
    simpa [prefixWord, tailWord_1316019, baseEnd_1316019] using wordTrace_append hprefix tailTrace_1316019
  have hstable : (prefixWord ++ tailWord_1316019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316019).length < 2 ^ (prefixWord ++ tailWord_1316019).sum := by decide
  have hdescent : baseEnd_1316019 < baseStart_1316019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316053 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 6]
def baseStart_1316053 : Nat := 118140960795 + 1316053 * 2 ^ 59
def prefixEnd_1316053 : Nat := 4983230072969 + 3 ^ 40 * 1316053 * 2
def baseEnd_1316053 : Nat := 150170612398143260063353

theorem tailTrace_1316053 : CollatzResearch.WordTrace tailWord_1316053 prefixEnd_1316053 150170612398143260063353 := by
  unfold tailWord_1316053
  simp only [CollatzResearch.WordTrace]
  refine ⟨48000396301172219803136813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32000264200781479868757875 48000396301172219803136813)
  ·
    refine ⟨18000148612939582426176305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48000396301172219803136813 18000148612939582426176305)
    ·
      refine ⟨13500111459704686819632229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18000148612939582426176305 13500111459704686819632229)
      ·
        refine ⟨2531270898694628778681043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13500111459704686819632229 2531270898694628778681043)
        ·
          refine ⟨3796906348041943168021565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531270898694628778681043 3796906348041943168021565)
          ·
            refine ⟨1423839880515728688008087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3796906348041943168021565 1423839880515728688008087)
            ·
              refine ⟨2135759820773593032012131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423839880515728688008087 2135759820773593032012131)
              ·
                refine ⟨3203639731160389548018197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2135759820773593032012131 3203639731160389548018197)
                ·
                  refine ⟨150170612398143260063353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3203639731160389548018197 150170612398143260063353)
                  ·
                    rfl

theorem cell22_1316053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_1316053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316053 prefixEnd_1316053 := by exact prefixLift 1316053
  have htrace : WordTrace (prefixWord ++ tailWord_1316053) baseStart_1316053 baseEnd_1316053 := by
    simpa [prefixWord, tailWord_1316053, baseEnd_1316053] using wordTrace_append hprefix tailTrace_1316053
  have hstable : (prefixWord ++ tailWord_1316053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316053).length < 2 ^ (prefixWord ++ tailWord_1316053).sum := by decide
  have hdescent : baseEnd_1316053 < baseStart_1316053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316064 : List Nat := [2, 1, 1, 3, 1, 4, 1, 9]
def baseStart_1316064 : Nat := 118140960795 + 1316064 * 2 ^ 59
def prefixEnd_1316064 : Nat := 4983230072969 + 3 ^ 40 * 1316064 * 2
def baseEnd_1316064 : Nat := 50057289191025490907225

theorem tailTrace_1316064 : CollatzResearch.WordTrace tailWord_1316064 prefixEnd_1316064 50057289191025490907225 := by
  unfold tailWord_1316064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000398752066184340893623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32000531669421579121191497 24000398752066184340893623)
  ·
    refine ⟨36000598128099276511340435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24000398752066184340893623 36000598128099276511340435)
    ·
      refine ⟨54000897192148914767010653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36000598128099276511340435 54000897192148914767010653)
      ·
        refine ⟨20250336447055843037628995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54000897192148914767010653 20250336447055843037628995)
        ·
          refine ⟨30375504670583764556443493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20250336447055843037628995 30375504670583764556443493)
          ·
            refine ⟨5695407125734455854333155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30375504670583764556443493 5695407125734455854333155)
            ·
              refine ⟨8543110688601683781499733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695407125734455854333155 8543110688601683781499733)
              ·
                refine ⟨50057289191025490907225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8543110688601683781499733 50057289191025490907225)
                ·
                  rfl

theorem cell22_1316064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_1316064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316064 prefixEnd_1316064 := by exact prefixLift 1316064
  have htrace : WordTrace (prefixWord ++ tailWord_1316064) baseStart_1316064 baseEnd_1316064 := by
    simpa [prefixWord, tailWord_1316064, baseEnd_1316064] using wordTrace_append hprefix tailTrace_1316064
  have hstable : (prefixWord ++ tailWord_1316064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316064).length < 2 ^ (prefixWord ++ tailWord_1316064).sum := by decide
  have hdescent : baseEnd_1316064 < baseStart_1316064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316098 : List Nat := [3, 4, 1, 1, 4, 9]
def baseStart_1316098 : Nat := 118140960795 + 1316098 * 2 ^ 59
def prefixEnd_1316098 : Nat := 4983230072969 + 3 ^ 40 * 1316098 * 2
def baseEnd_1316098 : Nat := 5562064711284748923641

theorem tailTrace_1316098 : CollatzResearch.WordTrace tailWord_1316098 prefixEnd_1316098 5562064711284748923641 := by
  unfold tailWord_1316098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12000509396502298122131237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32001358390672794992349965 12000509396502298122131237)
  ·
    refine ⟨2250095511844180897899607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12000509396502298122131237 2250095511844180897899607)
    ·
      refine ⟨3375143267766271346849411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2250095511844180897899607 3375143267766271346849411)
      ·
        refine ⟨5062714901649407020274117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3375143267766271346849411 5062714901649407020274117)
        ·
          refine ⟨949259044059263816301397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5062714901649407020274117 949259044059263816301397)
          ·
            refine ⟨5562064711284748923641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 949259044059263816301397 5562064711284748923641)
            ·
              rfl

theorem cell22_1316098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 9].length) (baseStart_1316098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316098 prefixEnd_1316098 := by exact prefixLift 1316098
  have htrace : WordTrace (prefixWord ++ tailWord_1316098) baseStart_1316098 baseEnd_1316098 := by
    simpa [prefixWord, tailWord_1316098, baseEnd_1316098] using wordTrace_append hprefix tailTrace_1316098
  have hstable : (prefixWord ++ tailWord_1316098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316098).length < 2 ^ (prefixWord ++ tailWord_1316098).sum := by decide
  have hdescent : baseEnd_1316098 < baseStart_1316098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316130 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1316130 : Nat := 118140960795 + 1316130 * 2 ^ 59
def prefixEnd_1316130 : Nat := 4983230072969 + 3 ^ 40 * 1316130 * 2
def baseEnd_1316130 : Nat := 450538195868027246014823

theorem tailTrace_1316130 : CollatzResearch.WordTrace tailWord_1316130 prefixEnd_1316130 450538195868027246014823 := by
  unfold tailWord_1316130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12000801180473315488422461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32002136481262174635793229 12000801180473315488422461)
  ·
    refine ⟨4500300442677493308158423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12000801180473315488422461 4500300442677493308158423)
    ·
      refine ⟨6750450664016239962237635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500300442677493308158423 6750450664016239962237635)
      ·
        refine ⟨10125675996024359943356453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6750450664016239962237635 10125675996024359943356453)
        ·
          refine ⟨1898564249254567489379335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10125675996024359943356453 1898564249254567489379335)
          ·
            refine ⟨2847846373881851234069003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898564249254567489379335 2847846373881851234069003)
            ·
              refine ⟨4271769560822776851103505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847846373881851234069003 4271769560822776851103505)
              ·
                refine ⟨3203827170617082638327629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4271769560822776851103505 3203827170617082638327629)
                ·
                  refine ⟨1201435188981405989372861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3203827170617082638327629 1201435188981405989372861)
                  ·
                    refine ⟨450538195868027246014823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1201435188981405989372861 450538195868027246014823)
                    ·
                      rfl

theorem cell22_1316130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1316130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316130 prefixEnd_1316130 := by exact prefixLift 1316130
  have htrace : WordTrace (prefixWord ++ tailWord_1316130) baseStart_1316130 baseEnd_1316130 := by
    simpa [prefixWord, tailWord_1316130, baseEnd_1316130] using wordTrace_append hprefix tailTrace_1316130
  have hstable : (prefixWord ++ tailWord_1316130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316130).length < 2 ^ (prefixWord ++ tailWord_1316130).sum := by decide
  have hdescent : baseEnd_1316130 < baseStart_1316130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316139 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 8]
def baseStart_1316139 : Nat := 118140960795 + 1316139 * 2 ^ 59
def prefixEnd_1316139 : Nat := 4983230072969 + 3 ^ 40 * 1316139 * 2
def baseEnd_1316139 : Nat := 450541276751954222539795

theorem tailTrace_1316139 : CollatzResearch.WordTrace tailWord_1316139 prefixEnd_1316139 450541276751954222539795 := by
  unfold tailWord_1316139
  simp only [CollatzResearch.WordTrace]
  refine ⟨48003532978860656490767471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32002355319240437660511647 48003532978860656490767471)
  ·
    refine ⟨72005299468290984736151207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48003532978860656490767471 72005299468290984736151207)
    ·
      refine ⟨108007949202436477104226811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72005299468290984736151207 108007949202436477104226811)
      ·
        refine ⟨162011923803654715656340217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108007949202436477104226811 162011923803654715656340217)
        ·
          refine ⟨121508942852741036742255163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162011923803654715656340217 121508942852741036742255163)
          ·
            refine ⟨182263414279111555113382745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121508942852741036742255163 182263414279111555113382745)
            ·
              refine ⟨136697560709333666335037059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182263414279111555113382745 136697560709333666335037059)
              ·
                refine ⟨205046341064000499502555589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136697560709333666335037059 205046341064000499502555589)
                ·
                  refine ⟨38446188949500093656729173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205046341064000499502555589 38446188949500093656729173)
                  ·
                    refine ⟨450541276751954222539795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38446188949500093656729173 450541276751954222539795)
                    ·
                      rfl

theorem cell22_1316139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_1316139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316139 prefixEnd_1316139 := by exact prefixLift 1316139
  have htrace : WordTrace (prefixWord ++ tailWord_1316139) baseStart_1316139 baseEnd_1316139 := by
    simpa [prefixWord, tailWord_1316139, baseEnd_1316139] using wordTrace_append hprefix tailTrace_1316139
  have hstable : (prefixWord ++ tailWord_1316139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316139).length < 2 ^ (prefixWord ++ tailWord_1316139).sum := by decide
  have hdescent : baseEnd_1316139 < baseStart_1316139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316205 : List Nat := [1, 5, 1, 1, 1, 3, 3, 3, 4]
def baseStart_1316205 : Nat := 118140960795 + 1316205 * 2 ^ 59
def prefixEnd_1316205 : Nat := 4983230072969 + 3 ^ 40 * 1316205 * 2
def baseEnd_1316205 : Nat := 150187956633584016796531

theorem tailTrace_1316205 : CollatzResearch.WordTrace tailWord_1316205 prefixEnd_1316205 150187956633584016796531 := by
  unfold tailWord_1316205
  simp only [CollatzResearch.WordTrace]
  refine ⟨48005940196621549762670069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32003960131081033175113379 48005940196621549762670069)
  ·
    refine ⟨4500556893433270290250319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48005940196621549762670069 4500556893433270290250319)
    ·
      refine ⟨6750835340149905435375479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500556893433270290250319 6750835340149905435375479)
      ·
        refine ⟨10126253010224858153063219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6750835340149905435375479 10126253010224858153063219)
        ·
          refine ⟨15189379515337287229594829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10126253010224858153063219 15189379515337287229594829)
          ·
            refine ⟨5696017318251482711098061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15189379515337287229594829 5696017318251482711098061)
            ·
              refine ⟨2136006494344306016661773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5696017318251482711098061 2136006494344306016661773)
              ·
                refine ⟨801002435379114756248165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2136006494344306016661773 801002435379114756248165)
                ·
                  refine ⟨150187956633584016796531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801002435379114756248165 150187956633584016796531)
                  ·
                    rfl

theorem cell22_1316205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_1316205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316205 prefixEnd_1316205 := by exact prefixLift 1316205
  have htrace : WordTrace (prefixWord ++ tailWord_1316205) baseStart_1316205 baseEnd_1316205 := by
    simpa [prefixWord, tailWord_1316205, baseEnd_1316205] using wordTrace_append hprefix tailTrace_1316205
  have hstable : (prefixWord ++ tailWord_1316205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316205).length < 2 ^ (prefixWord ++ tailWord_1316205).sum := by decide
  have hdescent : baseEnd_1316205 < baseStart_1316205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316233 : List Nat := [1, 2, 1, 1, 7, 1, 2, 7]
def baseStart_1316233 : Nat := 118140960795 + 1316233 * 2 ^ 59
def prefixEnd_1316233 : Nat := 4983230072969 + 3 ^ 40 * 1316233 * 2
def baseEnd_1316233 : Nat := 50063717208107701187723

theorem tailTrace_1316233 : CollatzResearch.WordTrace tailWord_1316233 prefixEnd_1316233 50063717208107701187723 := by
  unfold tailWord_1316233
  simp only [CollatzResearch.WordTrace]
  refine ⟨48006961440520110544689353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32004640960346740363126235 48006961440520110544689353)
  ·
    refine ⟨36005221080390082908517015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48006961440520110544689353 36005221080390082908517015)
    ·
      refine ⟨54007831620585124362775523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36005221080390082908517015 54007831620585124362775523)
      ·
        refine ⟨81011747430877686544163285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54007831620585124362775523 81011747430877686544163285)
        ·
          refine ⟨1898712830411195778378827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 81011747430877686544163285 1898712830411195778378827)
          ·
            refine ⟨2848069245616793667568241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898712830411195778378827 2848069245616793667568241)
            ·
              refine ⟨2136051934212595250676181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848069245616793667568241 2136051934212595250676181)
              ·
                refine ⟨50063717208107701187723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2136051934212595250676181 50063717208107701187723)
                ·
                  rfl

theorem cell22_1316233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 7].length) (baseStart_1316233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316233 prefixEnd_1316233 := by exact prefixLift 1316233
  have htrace : WordTrace (prefixWord ++ tailWord_1316233) baseStart_1316233 baseEnd_1316233 := by
    simpa [prefixWord, tailWord_1316233, baseEnd_1316233] using wordTrace_append hprefix tailTrace_1316233
  have hstable : (prefixWord ++ tailWord_1316233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316233).length < 2 ^ (prefixWord ++ tailWord_1316233).sum := by decide
  have hdescent : baseEnd_1316233 < baseStart_1316233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316252 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1316252 : Nat := 118140960795 + 1316252 * 2 ^ 59
def prefixEnd_1316252 : Nat := 4983230072969 + 3 ^ 40 * 1316252 * 2
def baseEnd_1316252 : Nat := 450579958961259594464449

theorem tailTrace_1316252 : CollatzResearch.WordTrace tailWord_1316252 prefixEnd_1316252 450579958961259594464449 := by
  unfold tailWord_1316252
  simp only [CollatzResearch.WordTrace]
  refine ⟨24003827213725638394815505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32005102951634184526420673 24003827213725638394815505)
  ·
    refine ⟨18002870410294228796111629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24003827213725638394815505 18002870410294228796111629)
    ·
      refine ⟨6751076403860335798541861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18002870410294228796111629 6751076403860335798541861)
      ·
        refine ⟨1265826825723812962226599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6751076403860335798541861 1265826825723812962226599)
        ·
          refine ⟨1898740238585719443339899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265826825723812962226599 1898740238585719443339899)
          ·
            refine ⟨2848110357878579165009849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898740238585719443339899 2848110357878579165009849)
            ·
              refine ⟨2136082768408934373757387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848110357878579165009849 2136082768408934373757387)
              ·
                refine ⟨3204124152613401560636081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136082768408934373757387 3204124152613401560636081)
                ·
                  refine ⟨2403093114460051170477061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3204124152613401560636081 2403093114460051170477061)
                  ·
                    refine ⟨450579958961259594464449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2403093114460051170477061 450579958961259594464449)
                    ·
                      rfl

theorem cell22_1316252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1316252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316252 prefixEnd_1316252 := by exact prefixLift 1316252
  have htrace : WordTrace (prefixWord ++ tailWord_1316252) baseStart_1316252 baseEnd_1316252 := by
    simpa [prefixWord, tailWord_1316252, baseEnd_1316252] using wordTrace_append hprefix tailTrace_1316252
  have hstable : (prefixWord ++ tailWord_1316252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316252).length < 2 ^ (prefixWord ++ tailWord_1316252).sum := by decide
  have hdescent : baseEnd_1316252 < baseStart_1316252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316261 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 7]
def baseStart_1316261 : Nat := 118140960795 + 1316261 * 2 ^ 59
def prefixEnd_1316261 : Nat := 4983230072969 + 3 ^ 40 * 1316261 * 2
def baseEnd_1316261 : Nat := 150194346615062190329807

theorem tailTrace_1316261 : CollatzResearch.WordTrace tailWord_1316261 prefixEnd_1316261 150194346615062190329807 := by
  unfold tailWord_1316261
  simp only [CollatzResearch.WordTrace]
  refine ⟨48007982684418671326708637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32005321789612447551139091 48007982684418671326708637)
  ·
    refine ⟨18002993506657001747515739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48007982684418671326708637 18002993506657001747515739)
    ·
      refine ⟨27004490259985502621273609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18002993506657001747515739 27004490259985502621273609)
      ·
        refine ⟨20253367694989126965955207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27004490259985502621273609 20253367694989126965955207)
        ·
          refine ⟨30380051542483690448932811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20253367694989126965955207 30380051542483690448932811)
          ·
            refine ⟨45570077313725535673399217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30380051542483690448932811 45570077313725535673399217)
            ·
              refine ⟨34177557985294151755049413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45570077313725535673399217 34177557985294151755049413)
              ·
                refine ⟨6408292122242653454071765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34177557985294151755049413 6408292122242653454071765)
                ·
                  refine ⟨150194346615062190329807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6408292122242653454071765 150194346615062190329807)
                  ·
                    rfl

theorem cell22_1316261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_1316261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316261 prefixEnd_1316261 := by exact prefixLift 1316261
  have htrace : WordTrace (prefixWord ++ tailWord_1316261) baseStart_1316261 baseEnd_1316261 := by
    simpa [prefixWord, tailWord_1316261, baseEnd_1316261] using wordTrace_append hprefix tailTrace_1316261
  have hstable : (prefixWord ++ tailWord_1316261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316261).length < 2 ^ (prefixWord ++ tailWord_1316261).sum := by decide
  have hdescent : baseEnd_1316261 < baseStart_1316261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316451 : List Nat := [1, 1, 1, 5, 1, 5, 2, 2, 1, 3]
def baseStart_1316451 : Nat := 118140960795 + 1316451 * 2 ^ 59
def prefixEnd_1316451 : Nat := 4983230072969 + 3 ^ 40 * 1316451 * 2
def baseEnd_1316451 : Nat := 450648080728089408738839

theorem tailTrace_1316451 : CollatzResearch.WordTrace tailWord_1316451 prefixEnd_1316451 450648080728089408738839 := by
  unfold tailWord_1316451
  simp only [CollatzResearch.WordTrace]
  refine ⟨48014912553730333776125207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32009941702486889184083471 48014912553730333776125207)
  ·
    refine ⟨72022368830595500664187811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48014912553730333776125207 72022368830595500664187811)
    ·
      refine ⟨108033553245893250996281717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72022368830595500664187811 108033553245893250996281717)
      ·
        refine ⟨10128145616802492280901411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108033553245893250996281717 10128145616802492280901411)
        ·
          refine ⟨15192218425203738421352117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10128145616802492280901411 15192218425203738421352117)
          ·
            refine ⟨1424270477362850477001761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15192218425203738421352117 1424270477362850477001761)
            ·
              refine ⟨1068202858022137857751321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424270477362850477001761 1068202858022137857751321)
              ·
                refine ⟨801152143516603393313491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068202858022137857751321 801152143516603393313491)
                ·
                  refine ⟨1201728215274905089970237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801152143516603393313491 1201728215274905089970237)
                  ·
                    refine ⟨450648080728089408738839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1201728215274905089970237 450648080728089408738839)
                    ·
                      rfl

theorem cell22_1316451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 1, 3].length) (baseStart_1316451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316451 prefixEnd_1316451 := by exact prefixLift 1316451
  have htrace : WordTrace (prefixWord ++ tailWord_1316451) baseStart_1316451 baseEnd_1316451 := by
    simpa [prefixWord, tailWord_1316451, baseEnd_1316451] using wordTrace_append hprefix tailTrace_1316451
  have hstable : (prefixWord ++ tailWord_1316451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316451).length < 2 ^ (prefixWord ++ tailWord_1316451).sum := by decide
  have hdescent : baseEnd_1316451 < baseStart_1316451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316462 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1316462 : Nat := 118140960795 + 1316462 * 2 ^ 59
def prefixEnd_1316462 : Nat := 4983230072969 + 3 ^ 40 * 1316462 * 2
def baseEnd_1316462 : Nat := 450651846252889046713805

theorem tailTrace_1316462 : CollatzResearch.WordTrace tailWord_1316462 prefixEnd_1316462 450651846252889046713805 := by
  unfold tailWord_1316462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001914219586310331846955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32010209171126988436517093 6001914219586310331846955)
  ·
    refine ⟨9002871329379465497770433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6001914219586310331846955 9002871329379465497770433)
    ·
      refine ⟨6752153497034599123327825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9002871329379465497770433 6752153497034599123327825)
      ·
        refine ⟨5064115122775949342495869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6752153497034599123327825 5064115122775949342495869)
        ·
          refine ⟨1899043171040981003435951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5064115122775949342495869 1899043171040981003435951)
          ·
            refine ⟨2848564756561471505153927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899043171040981003435951 2848564756561471505153927)
            ·
              refine ⟨4272847134842207257730891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848564756561471505153927 4272847134842207257730891)
              ·
                refine ⟨6409270702263310886596337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272847134842207257730891 6409270702263310886596337)
                ·
                  refine ⟨4806953026697483164947253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6409270702263310886596337 4806953026697483164947253)
                  ·
                    refine ⟨450651846252889046713805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4806953026697483164947253 450651846252889046713805)
                    ·
                      rfl

theorem cell22_1316462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1316462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316462 prefixEnd_1316462 := by exact prefixLift 1316462
  have htrace : WordTrace (prefixWord ++ tailWord_1316462) baseStart_1316462 baseEnd_1316462 := by
    simpa [prefixWord, tailWord_1316462, baseEnd_1316462] using wordTrace_append hprefix tailTrace_1316462
  have hstable : (prefixWord ++ tailWord_1316462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316462).length < 2 ^ (prefixWord ++ tailWord_1316462).sum := by decide
  have hdescent : baseEnd_1316462 < baseStart_1316462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316492 : List Nat := [2, 2, 1, 2, 1, 1, 6, 3, 4]
def baseStart_1316492 : Nat := 118140960795 + 1316492 * 2 ^ 59
def prefixEnd_1316492 : Nat := 4983230072969 + 3 ^ 40 * 1316492 * 2
def baseEnd_1316492 : Nat := 150220705288659656154571

theorem tailTrace_1316492 : CollatzResearch.WordTrace tailWord_1316492 prefixEnd_1316492 150220705288659656154571 := by
  unfold tailWord_1316492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24008203973290898889183865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32010938631054531852245153 24008203973290898889183865)
  ·
    refine ⟨18006152979968174166887899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24008203973290898889183865 18006152979968174166887899)
    ·
      refine ⟨27009229469952261250331849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18006152979968174166887899 27009229469952261250331849)
      ·
        refine ⟨20256922102464195937748887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27009229469952261250331849 20256922102464195937748887)
        ·
          refine ⟨30385383153696293906623331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20256922102464195937748887 30385383153696293906623331)
          ·
            refine ⟨45578074730544440859934997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30385383153696293906623331 45578074730544440859934997)
            ·
              refine ⟨2136472252994270665309453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45578074730544440859934997 2136472252994270665309453)
              ·
                refine ⟨801177094872851499491045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2136472252994270665309453 801177094872851499491045)
                ·
                  refine ⟨150220705288659656154571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801177094872851499491045 150220705288659656154571)
                  ·
                    rfl

theorem cell22_1316492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_1316492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316492 prefixEnd_1316492 := by exact prefixLift 1316492
  have htrace : WordTrace (prefixWord ++ tailWord_1316492) baseStart_1316492 baseEnd_1316492 := by
    simpa [prefixWord, tailWord_1316492, baseEnd_1316492] using wordTrace_append hprefix tailTrace_1316492
  have hstable : (prefixWord ++ tailWord_1316492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316492).length < 2 ^ (prefixWord ++ tailWord_1316492).sum := by decide
  have hdescent : baseEnd_1316492 < baseStart_1316492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316494 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_1316494 : Nat := 118140960795 + 1316494 * 2 ^ 59
def prefixEnd_1316494 : Nat := 4983230072969 + 3 ^ 40 * 1316494 * 2
def baseEnd_1316494 : Nat := 450662800506851629913707

theorem tailTrace_1316494 : CollatzResearch.WordTrace tailWord_1316494 prefixEnd_1316494 450662800506851629913707 := by
  unfold tailWord_1316494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6002060111571819014992567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32010987261716368079960357 6002060111571819014992567)
  ·
    refine ⟨9003090167357728522488851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6002060111571819014992567 9003090167357728522488851)
    ·
      refine ⟨13504635251036592783733277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9003090167357728522488851 13504635251036592783733277)
      ·
        refine ⟨5064238219138722293899979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13504635251036592783733277 5064238219138722293899979)
        ·
          refine ⟨7596357328708083440849969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064238219138722293899979 7596357328708083440849969)
          ·
            refine ⟨5697267996531062580637477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7596357328708083440849969 5697267996531062580637477)
            ·
              refine ⟨1068237749349574233869527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5697267996531062580637477 1068237749349574233869527)
              ·
                refine ⟨1602356624024361350804291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068237749349574233869527 1602356624024361350804291)
                ·
                  refine ⟨2403534936036542026206437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1602356624024361350804291 2403534936036542026206437)
                  ·
                    refine ⟨450662800506851629913707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2403534936036542026206437 450662800506851629913707)
                    ·
                      rfl

theorem cell22_1316494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_1316494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316494 prefixEnd_1316494 := by exact prefixLift 1316494
  have htrace : WordTrace (prefixWord ++ tailWord_1316494) baseStart_1316494 baseEnd_1316494 := by
    simpa [prefixWord, tailWord_1316494, baseEnd_1316494] using wordTrace_append hprefix tailTrace_1316494
  have hstable : (prefixWord ++ tailWord_1316494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316494).length < 2 ^ (prefixWord ++ tailWord_1316494).sum := by decide
  have hdescent : baseEnd_1316494 < baseStart_1316494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316569 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 3, 3]
def baseStart_1316569 : Nat := 118140960795 + 1316569 * 2 ^ 59
def prefixEnd_1316569 : Nat := 4983230072969 + 3 ^ 40 * 1316569 * 2
def baseEnd_1316569 : Nat := 450688474539576434288477

theorem tailTrace_1316569 : CollatzResearch.WordTrace tailWord_1316569 prefixEnd_1316569 450688474539576434288477 := by
  unfold tailWord_1316569
  simp only [CollatzResearch.WordTrace]
  refine ⟨48019216367302839928920761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32012810911535226619280507 48019216367302839928920761)
  ·
    refine ⟨36014412275477129946690571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48019216367302839928920761 36014412275477129946690571)
    ·
      refine ⟨54021618413215694920035857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36014412275477129946690571 54021618413215694920035857)
      ·
        refine ⟨40516213809911771190026893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54021618413215694920035857 40516213809911771190026893)
        ·
          refine ⟨15193580178716914196260085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40516213809911771190026893 15193580178716914196260085)
          ·
            refine ⟨1424398141754710705899383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15193580178716914196260085 1424398141754710705899383)
            ·
              refine ⟨2136597212632066058849075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424398141754710705899383 2136597212632066058849075)
              ·
                refine ⟨3204895818948099088273613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136597212632066058849075 3204895818948099088273613)
                ·
                  refine ⟨1201835932105537158102605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3204895818948099088273613 1201835932105537158102605)
                  ·
                    refine ⟨450688474539576434288477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1201835932105537158102605 450688474539576434288477)
                    ·
                      rfl

theorem cell22_1316569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_1316569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316569 prefixEnd_1316569 := by exact prefixLift 1316569
  have htrace : WordTrace (prefixWord ++ tailWord_1316569) baseStart_1316569 baseEnd_1316569 := by
    simpa [prefixWord, tailWord_1316569, baseEnd_1316569] using wordTrace_append hprefix tailTrace_1316569
  have hstable : (prefixWord ++ tailWord_1316569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316569).length < 2 ^ (prefixWord ++ tailWord_1316569).sum := by decide
  have hdescent : baseEnd_1316569 < baseStart_1316569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316580 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1316580 : Nat := 118140960795 + 1316580 * 2 ^ 59
def prefixEnd_1316580 : Nat := 4983230072969 + 3 ^ 40 * 1316580 * 2
def baseEnd_1316580 : Nat := 450692240064376072263443

theorem tailTrace_1316580 : CollatzResearch.WordTrace tailWord_1316580 prefixEnd_1316580 450692240064376072263443 := by
  unfold tailWord_1316580
  simp only [CollatzResearch.WordTrace]
  refine ⟨24009808785131494403785597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32013078380175325871714129 24009808785131494403785597)
  ·
    refine ⟨9003678294424310401419599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24009808785131494403785597 9003678294424310401419599)
    ·
      refine ⟨13505517441636465602129399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9003678294424310401419599 13505517441636465602129399)
      ·
        refine ⟨20258276162454698403194099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13505517441636465602129399 20258276162454698403194099)
        ·
          refine ⟨30387414243682047604791149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20258276162454698403194099 30387414243682047604791149)
          ·
            refine ⟨11395280341380767851796681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30387414243682047604791149 11395280341380767851796681)
            ·
              refine ⟨8546460256035575888847511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11395280341380767851796681 8546460256035575888847511)
              ·
                refine ⟨12819690384053363833271267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8546460256035575888847511 12819690384053363833271267)
                ·
                  refine ⟨19229535576080045749906901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12819690384053363833271267 19229535576080045749906901)
                  ·
                    refine ⟨450692240064376072263443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19229535576080045749906901 450692240064376072263443)
                    ·
                      rfl

theorem cell22_1316580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1316580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316580 prefixEnd_1316580 := by exact prefixLift 1316580
  have htrace : WordTrace (prefixWord ++ tailWord_1316580) baseStart_1316580 baseEnd_1316580 := by
    simpa [prefixWord, tailWord_1316580, baseEnd_1316580] using wordTrace_append hprefix tailTrace_1316580
  have hstable : (prefixWord ++ tailWord_1316580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316580).length < 2 ^ (prefixWord ++ tailWord_1316580).sum := by decide
  have hdescent : baseEnd_1316580 < baseStart_1316580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316625 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1316625 : Nat := 118140960795 + 1316625 * 2 ^ 59
def prefixEnd_1316625 : Nat := 4983230072969 + 3 ^ 40 * 1316625 * 2
def baseEnd_1316625 : Nat := 450707644484010954888305

theorem tailTrace_1316625 : CollatzResearch.WordTrace tailWord_1316625 prefixEnd_1316625 450707644484010954888305 := by
  unfold tailWord_1316625
  simp only [CollatzResearch.WordTrace]
  refine ⟨48021258855099961492959329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32014172570066640995306219 48021258855099961492959329)
  ·
    refine ⟨36015944141324971119719497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48021258855099961492959329 36015944141324971119719497)
    ·
      refine ⟨27011958105993728339789623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36015944141324971119719497 27011958105993728339789623)
      ·
        refine ⟨40517937158990592509684435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27011958105993728339789623 40517937158990592509684435)
        ·
          refine ⟨60776905738485888764526653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40517937158990592509684435 60776905738485888764526653)
          ·
            refine ⟨22791339651932208286697495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60776905738485888764526653 22791339651932208286697495)
            ·
              refine ⟨34187009477898312430046243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22791339651932208286697495 34187009477898312430046243)
              ·
                refine ⟨51280514216847468645069365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34187009477898312430046243 51280514216847468645069365)
                ·
                  refine ⟨4807548207829450185475253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51280514216847468645069365 4807548207829450185475253)
                  ·
                    refine ⟨450707644484010954888305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4807548207829450185475253 450707644484010954888305)
                    ·
                      rfl

theorem cell22_1316625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1316625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316625 prefixEnd_1316625 := by exact prefixLift 1316625
  have htrace : WordTrace (prefixWord ++ tailWord_1316625) baseStart_1316625 baseEnd_1316625 := by
    simpa [prefixWord, tailWord_1316625, baseEnd_1316625] using wordTrace_append hprefix tailTrace_1316625
  have hstable : (prefixWord ++ tailWord_1316625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316625).length < 2 ^ (prefixWord ++ tailWord_1316625).sum := by decide
  have hdescent : baseEnd_1316625 < baseStart_1316625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316657 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_1316657 : Nat := 118140960795 + 1316657 * 2 ^ 59
def prefixEnd_1316657 : Nat := 4983230072969 + 3 ^ 40 * 1316657 * 2
def baseEnd_1316657 : Nat := 450718598737973538088207

theorem tailTrace_1316657 : CollatzResearch.WordTrace tailWord_1316657 prefixEnd_1316657 450718598737973538088207 := by
  unfold tailWord_1316657
  simp only [CollatzResearch.WordTrace]
  refine ⟨48022425990984030958124225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32014950660656020638749483 48022425990984030958124225)
  ·
    refine ⟨36016819493238023218593169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48022425990984030958124225 36016819493238023218593169)
    ·
      refine ⟨27012614619928517413944877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36016819493238023218593169 27012614619928517413944877)
      ·
        refine ⟨10129730482473194030229329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27012614619928517413944877 10129730482473194030229329)
        ·
          refine ⟨7597297861854895522671997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10129730482473194030229329 7597297861854895522671997)
          ·
            refine ⟨2848986698195585821001999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7597297861854895522671997 2848986698195585821001999)
            ·
              refine ⟨4273480047293378731502999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848986698195585821001999 4273480047293378731502999)
              ·
                refine ⟨6410220070940068097254499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273480047293378731502999 6410220070940068097254499)
                ·
                  refine ⟨9615330106410102145881749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6410220070940068097254499 9615330106410102145881749)
                  ·
                    refine ⟨450718598737973538088207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9615330106410102145881749 450718598737973538088207)
                    ·
                      rfl

theorem cell22_1316657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_1316657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316657 prefixEnd_1316657 := by exact prefixLift 1316657
  have htrace : WordTrace (prefixWord ++ tailWord_1316657) baseStart_1316657 baseEnd_1316657 := by
    simpa [prefixWord, tailWord_1316657, baseEnd_1316657] using wordTrace_append hprefix tailTrace_1316657
  have hstable : (prefixWord ++ tailWord_1316657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316657).length < 2 ^ (prefixWord ++ tailWord_1316657).sum := by decide
  have hdescent : baseEnd_1316657 < baseStart_1316657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316661 : List Nat := [1, 3, 3, 1, 4, 1, 2, 3, 4]
def baseStart_1316661 : Nat := 118140960795 + 1316661 * 2 ^ 59
def prefixEnd_1316661 : Nat := 4983230072969 + 3 ^ 40 * 1316661 * 2
def baseEnd_1316661 : Nat := 150239989339906286996065

theorem tailTrace_1316661 : CollatzResearch.WordTrace tailWord_1316661 prefixEnd_1316661 150239989339906286996065 := by
  unfold tailWord_1316661
  simp only [CollatzResearch.WordTrace]
  refine ⟨48022571882969539641269837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32015047921979693094179891 48022571882969539641269837)
  ·
    refine ⟨18008464456113577365476189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48022571882969539641269837 18008464456113577365476189)
    ·
      refine ⟨6753174171042591512053571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18008464456113577365476189 6753174171042591512053571)
      ·
        refine ⟨10129761256563887268080357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6753174171042591512053571 10129761256563887268080357)
        ·
          refine ⟨1899330235605728862765067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10129761256563887268080357 1899330235605728862765067)
          ·
            refine ⟨2848995353408593294147601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899330235605728862765067 2848995353408593294147601)
            ·
              refine ⟨2136746515056444970610701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848995353408593294147601 2136746515056444970610701)
              ·
                refine ⟨801279943146166863979013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2136746515056444970610701 801279943146166863979013)
                ·
                  refine ⟨150239989339906286996065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801279943146166863979013 150239989339906286996065)
                  ·
                    rfl

theorem cell22_1316661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_1316661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316661 prefixEnd_1316661 := by exact prefixLift 1316661
  have htrace : WordTrace (prefixWord ++ tailWord_1316661) baseStart_1316661 baseEnd_1316661 := by
    simpa [prefixWord, tailWord_1316661, baseEnd_1316661] using wordTrace_append hprefix tailTrace_1316661
  have hstable : (prefixWord ++ tailWord_1316661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316661).length < 2 ^ (prefixWord ++ tailWord_1316661).sum := by decide
  have hdescent : baseEnd_1316661 < baseStart_1316661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316678 : List Nat := [6, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1316678 : Nat := 118140960795 + 1316678 * 2 ^ 59
def prefixEnd_1316678 : Nat := 4983230072969 + 3 ^ 40 * 1316678 * 2
def baseEnd_1316678 : Nat := 150241929155712161104381

theorem tailTrace_1316678 : CollatzResearch.WordTrace tailWord_1316678 prefixEnd_1316678 150241929155712161104381 := by
  unfold tailWord_1316678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500724747622123485769959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32015461282605301029759125 1500724747622123485769959)
  ·
    refine ⟨2251087121433185228654939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1500724747622123485769959 2251087121433185228654939)
    ·
      refine ⟨3376630682149777842982409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2251087121433185228654939 3376630682149777842982409)
      ·
        refine ⟨2532473011612333382236807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3376630682149777842982409 2532473011612333382236807)
        ·
          refine ⟨3798709517418500073355211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532473011612333382236807 3798709517418500073355211)
          ·
            refine ⟨5698064276127750110032817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798709517418500073355211 5698064276127750110032817)
            ·
              refine ⟨4273548207095812582524613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5698064276127750110032817 4273548207095812582524613)
              ·
                refine ⟨801290288830464859223365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4273548207095812582524613 801290288830464859223365)
                ·
                  refine ⟨150241929155712161104381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801290288830464859223365 150241929155712161104381)
                  ·
                    rfl

theorem cell22_1316678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1316678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316678 prefixEnd_1316678 := by exact prefixLift 1316678
  have htrace : WordTrace (prefixWord ++ tailWord_1316678) baseStart_1316678 baseEnd_1316678 := by
    simpa [prefixWord, tailWord_1316678, baseEnd_1316678] using wordTrace_append hprefix tailTrace_1316678
  have hstable : (prefixWord ++ tailWord_1316678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316678).length < 2 ^ (prefixWord ++ tailWord_1316678).sum := by decide
  have hdescent : baseEnd_1316678 < baseStart_1316678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316704 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 3, 3]
def baseStart_1316704 : Nat := 118140960795 + 1316704 * 2 ^ 59
def prefixEnd_1316704 : Nat := 4983230072969 + 3 ^ 40 * 1316704 * 2
def baseEnd_1316704 : Nat := 450734687798481082163063

theorem tailTrace_1316704 : CollatzResearch.WordTrace tailWord_1316704 prefixEnd_1316704 450734687798481082163063 := by
  unfold tailWord_1316704
  simp only [CollatzResearch.WordTrace]
  refine ⟨24012070110906878992542583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32016093481209171990056777 24012070110906878992542583)
  ·
    refine ⟨36018105166360318488813875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24012070110906878992542583 36018105166360318488813875)
    ·
      refine ⟨54027157749540477733220813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36018105166360318488813875 54027157749540477733220813)
      ·
        refine ⟨20260184156077679149957805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54027157749540477733220813 20260184156077679149957805)
        ·
          refine ⟨7597569058529129681234177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20260184156077679149957805 7597569058529129681234177)
          ·
            refine ⟨5698176793896847260925633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7597569058529129681234177 5698176793896847260925633)
            ·
              refine ⟨4273632595422635445694225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5698176793896847260925633 4273632595422635445694225)
              ·
                refine ⟨3205224446566976584270669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4273632595422635445694225 3205224446566976584270669)
                ·
                  refine ⟨1201959167462616219101501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3205224446566976584270669 1201959167462616219101501)
                  ·
                    refine ⟨450734687798481082163063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1201959167462616219101501 450734687798481082163063)
                    ·
                      rfl

theorem cell22_1316704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_1316704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316704 prefixEnd_1316704 := by exact prefixLift 1316704
  have htrace : WordTrace (prefixWord ++ tailWord_1316704) baseStart_1316704 baseEnd_1316704 := by
    simpa [prefixWord, tailWord_1316704, baseEnd_1316704] using wordTrace_append hprefix tailTrace_1316704
  have hstable : (prefixWord ++ tailWord_1316704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316704).length < 2 ^ (prefixWord ++ tailWord_1316704).sum := by decide
  have hdescent : baseEnd_1316704 < baseStart_1316704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316706 : List Nat := [3, 3, 2, 1, 2, 3, 2, 6]
def baseStart_1316706 : Nat := 118140960795 + 1316706 * 2 ^ 59
def prefixEnd_1316706 : Nat := 4983230072969 + 3 ^ 40 * 1316706 * 2
def baseEnd_1316706 : Nat := 50081708048817082623673

theorem tailTrace_1316706 : CollatzResearch.WordTrace tailWord_1316706 prefixEnd_1316706 50081708048817082623673 := by
  unfold tailWord_1316706
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006053291951628081664493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32016142111871008217771981 12006053291951628081664493)
  ·
    refine ⟨4502269984481860530624185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12006053291951628081664493 4502269984481860530624185)
    ·
      refine ⟨3376702488361395397968139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4502269984481860530624185 3376702488361395397968139)
      ·
        refine ⟨5065053732542093096952209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3376702488361395397968139 5065053732542093096952209)
        ·
          refine ⟨3798790299406569822714157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5065053732542093096952209 3798790299406569822714157)
          ·
            refine ⟨1424546362277463683517809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3798790299406569822714157 1424546362277463683517809)
            ·
              refine ⟨1068409771708097762638357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424546362277463683517809 1068409771708097762638357)
              ·
                refine ⟨50081708048817082623673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1068409771708097762638357 50081708048817082623673)
                ·
                  rfl

theorem cell22_1316706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_1316706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316706 prefixEnd_1316706 := by exact prefixLift 1316706
  have htrace : WordTrace (prefixWord ++ tailWord_1316706) baseStart_1316706 baseEnd_1316706 := by
    simpa [prefixWord, tailWord_1316706, baseEnd_1316706] using wordTrace_append hprefix tailTrace_1316706
  have hstable : (prefixWord ++ tailWord_1316706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316706).length < 2 ^ (prefixWord ++ tailWord_1316706).sum := by decide
  have hdescent : baseEnd_1316706 < baseStart_1316706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316717 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 7]
def baseStart_1316717 : Nat := 118140960795 + 1316717 * 2 ^ 59
def prefixEnd_1316717 : Nat := 4983230072969 + 3 ^ 40 * 1316717 * 2
def baseEnd_1316717 : Nat := 150246379321384460529341

theorem tailTrace_1316717 : CollatzResearch.WordTrace tailWord_1316717 prefixEnd_1316717 150246379321384460529341 := by
  unfold tailWord_1316717
  simp only [CollatzResearch.WordTrace]
  refine ⟨48024614370766661205308405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32016409580511107470205603 48024614370766661205308405)
  ·
    refine ⟨4502307597259374487997663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48024614370766661205308405 4502307597259374487997663)
    ·
      refine ⟨6753461395889061731996495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4502307597259374487997663 6753461395889061731996495)
      ·
        refine ⟨10130192093833592597994743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6753461395889061731996495 10130192093833592597994743)
        ·
          refine ⟨15195288140750388896992115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10130192093833592597994743 15195288140750388896992115)
          ·
            refine ⟨22792932211125583345488173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15195288140750388896992115 22792932211125583345488173)
            ·
              refine ⟨8547349579172093754558065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22792932211125583345488173 8547349579172093754558065)
              ·
                refine ⟨6410512184379070315918549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8547349579172093754558065 6410512184379070315918549)
                ·
                  refine ⟨150246379321384460529341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6410512184379070315918549 150246379321384460529341)
                  ·
                    rfl

theorem cell22_1316717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_1316717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316717 prefixEnd_1316717 := by exact prefixLift 1316717
  have htrace : WordTrace (prefixWord ++ tailWord_1316717) baseStart_1316717 baseEnd_1316717 := by
    simpa [prefixWord, tailWord_1316717, baseEnd_1316717] using wordTrace_append hprefix tailTrace_1316717
  have hstable : (prefixWord ++ tailWord_1316717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316717).length < 2 ^ (prefixWord ++ tailWord_1316717).sum := by decide
  have hdescent : baseEnd_1316717 < baseStart_1316717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316747 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 3, 4]
def baseStart_1316747 : Nat := 118140960795 + 1316747 * 2 ^ 59
def prefixEnd_1316747 : Nat := 4983230072969 + 3 ^ 40 * 1316747 * 2
def baseEnd_1316747 : Nat := 450749407577243303337931

theorem tailTrace_1316747 : CollatzResearch.WordTrace tailWord_1316747 prefixEnd_1316747 450749407577243303337931 := by
  unfold tailWord_1316747
  simp only [CollatzResearch.WordTrace]
  refine ⟨48025708560657976328900495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32017139040438650885933663 48025708560657976328900495)
  ·
    refine ⟨72038562840986964493350743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48025708560657976328900495 72038562840986964493350743)
    ·
      refine ⟨108057844261480446740026115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72038562840986964493350743 108057844261480446740026115)
      ·
        refine ⟨162086766392220670110039173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108057844261480446740026115 162086766392220670110039173)
        ·
          refine ⟨30391268698541375645632345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162086766392220670110039173 30391268698541375645632345)
          ·
            refine ⟨22793451523906031734224259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30391268698541375645632345 22793451523906031734224259)
            ·
              refine ⟨34190177285859047601336389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22793451523906031734224259 34190177285859047601336389)
              ·
                refine ⟨6410658241098571425250573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34190177285859047601336389 6410658241098571425250573)
                ·
                  refine ⟨2403996840411964284468965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6410658241098571425250573 2403996840411964284468965)
                  ·
                    refine ⟨450749407577243303337931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2403996840411964284468965 450749407577243303337931)
                    ·
                      rfl

theorem cell22_1316747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_1316747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316747 prefixEnd_1316747 := by exact prefixLift 1316747
  have htrace : WordTrace (prefixWord ++ tailWord_1316747) baseStart_1316747 baseEnd_1316747 := by
    simpa [prefixWord, tailWord_1316747, baseEnd_1316747] using wordTrace_append hprefix tailTrace_1316747
  have hstable : (prefixWord ++ tailWord_1316747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316747).length < 2 ^ (prefixWord ++ tailWord_1316747).sum := by decide
  have hdescent : baseEnd_1316747 < baseStart_1316747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316824 : List Nat := [2, 1, 2, 2, 2, 2, 5, 6]
def baseStart_1316824 : Nat := 118140960795 + 1316824 * 2 ^ 59
def prefixEnd_1316824 : Nat := 4983230072969 + 3 ^ 40 * 1316824 * 2
def baseEnd_1316824 : Nat := 50086196250093418795855

theorem tailTrace_1316824 : CollatzResearch.WordTrace tailWord_1316824 prefixEnd_1316824 50086196250093418795855 := by
  unfold tailWord_1316824
  simp only [CollatzResearch.WordTrace]
  refine ⟨24014258490689509239726763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32019011320919345652969017 24014258490689509239726763)
  ·
    refine ⟨36021387736034263859590145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24014258490689509239726763 36021387736034263859590145)
    ·
      refine ⟨27016040802025697894692609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36021387736034263859590145 27016040802025697894692609)
      ·
        refine ⟨20262030601519273421019457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27016040802025697894692609 20262030601519273421019457)
        ·
          refine ⟨15196522951139455065764593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20262030601519273421019457 15196522951139455065764593)
          ·
            refine ⟨11397392213354591299323445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15196522951139455065764593 11397392213354591299323445)
            ·
              refine ⟨1068505520001992934311573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11397392213354591299323445 1068505520001992934311573)
              ·
                refine ⟨50086196250093418795855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1068505520001992934311573 50086196250093418795855)
                ·
                  rfl

theorem cell22_1316824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 6].length) (baseStart_1316824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316824 prefixEnd_1316824 := by exact prefixLift 1316824
  have htrace : WordTrace (prefixWord ++ tailWord_1316824) baseStart_1316824 baseEnd_1316824 := by
    simpa [prefixWord, tailWord_1316824, baseEnd_1316824] using wordTrace_append hprefix tailTrace_1316824
  have hstable : (prefixWord ++ tailWord_1316824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316824).length < 2 ^ (prefixWord ++ tailWord_1316824).sum := by decide
  have hdescent : baseEnd_1316824 < baseStart_1316824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316890 : List Nat := [3, 1, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_1316890 : Nat := 118140960795 + 1316890 * 2 ^ 59
def prefixEnd_1316890 : Nat := 4983230072969 + 3 ^ 40 * 1316890 * 2
def baseEnd_1316890 : Nat := 450798359399638597012493

theorem tailTrace_1316890 : CollatzResearch.WordTrace tailWord_1316890 prefixEnd_1316890 450798359399638597012493 := by
  unfold tailWord_1316890
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007731049784977937839031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32020616132759941167570749 12007731049784977937839031)
  ·
    refine ⟨18011596574677466906758547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12007731049784977937839031 18011596574677466906758547)
    ·
      refine ⟨27017394862016200360137821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18011596574677466906758547 27017394862016200360137821)
      ·
        refine ⟨10131523073256075135051683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27017394862016200360137821 10131523073256075135051683)
        ·
          refine ⟨15197284609884112702577525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10131523073256075135051683 15197284609884112702577525)
          ·
            refine ⟨1424745432176635565866643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15197284609884112702577525 1424745432176635565866643)
            ·
              refine ⟨2137118148264953348799965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424745432176635565866643 2137118148264953348799965)
              ·
                refine ⟨801419305599357505799987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137118148264953348799965 801419305599357505799987)
                ·
                  refine ⟨1202128958399036258699981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801419305599357505799987 1202128958399036258699981)
                  ·
                    refine ⟨450798359399638597012493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202128958399036258699981 450798359399638597012493)
                    ·
                      rfl

theorem cell22_1316890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_1316890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316890 prefixEnd_1316890 := by exact prefixLift 1316890
  have htrace : WordTrace (prefixWord ++ tailWord_1316890) baseStart_1316890 baseEnd_1316890 := by
    simpa [prefixWord, tailWord_1316890, baseEnd_1316890] using wordTrace_append hprefix tailTrace_1316890
  have hstable : (prefixWord ++ tailWord_1316890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316890).length < 2 ^ (prefixWord ++ tailWord_1316890).sum := by decide
  have hdescent : baseEnd_1316890 < baseStart_1316890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316920 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 5]
def baseStart_1316920 : Nat := 118140960795 + 1316920 * 2 ^ 59
def prefixEnd_1316920 : Nat := 4983230072969 + 3 ^ 40 * 1316920 * 2
def baseEnd_1316920 : Nat := 150269543004242839587467

theorem tailTrace_1316920 : CollatzResearch.WordTrace tailWord_1316920 prefixEnd_1316920 150269543004242839587467 := by
  unfold tailWord_1316920
  simp only [CollatzResearch.WordTrace]
  refine ⟨24016009194515613437474107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32021345592687484583298809 24016009194515613437474107)
  ·
    refine ⟨36024013791773420156211161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24016009194515613437474107 36024013791773420156211161)
    ·
      refine ⟨27018010343830065117158371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36024013791773420156211161 27018010343830065117158371)
      ·
        refine ⟨40527015515745097675737557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27018010343830065117158371 40527015515745097675737557)
        ·
          refine ⟨949851926150275726775099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 40527015515745097675737557 949851926150275726775099)
          ·
            refine ⟨1424777889225413590162649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949851926150275726775099 1424777889225413590162649)
            ·
              refine ⟨1068583416919060192621987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424777889225413590162649 1068583416919060192621987)
              ·
                refine ⟨1602875125378590288932981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068583416919060192621987 1602875125378590288932981)
                ·
                  refine ⟨150269543004242839587467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1602875125378590288932981 150269543004242839587467)
                  ·
                    rfl

theorem cell22_1316920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_1316920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316920 prefixEnd_1316920 := by exact prefixLift 1316920
  have htrace : WordTrace (prefixWord ++ tailWord_1316920) baseStart_1316920 baseEnd_1316920 := by
    simpa [prefixWord, tailWord_1316920, baseEnd_1316920] using wordTrace_append hprefix tailTrace_1316920
  have hstable : (prefixWord ++ tailWord_1316920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316920).length < 2 ^ (prefixWord ++ tailWord_1316920).sum := by decide
  have hdescent : baseEnd_1316920 < baseStart_1316920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316958 : List Nat := [4, 4, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1316958 : Nat := 118140960795 + 1316958 * 2 ^ 59
def prefixEnd_1316958 : Nat := 4983230072969 + 3 ^ 40 * 1316958 * 2
def baseEnd_1316958 : Nat := 450821637189309086312285

theorem tailTrace_1316958 : CollatzResearch.WordTrace tailWord_1316958 prefixEnd_1316958 450821637189309086312285 := by
  unfold tailWord_1316958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6004175545361694920603941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32022269575262372909887685 6004175545361694920603941)
  ·
    refine ⟨1125782914755317797613239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6004175545361694920603941 1125782914755317797613239)
    ·
      refine ⟨1688674372132976696419859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125782914755317797613239 1688674372132976696419859)
      ·
        refine ⟨2533011558199465044629789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688674372132976696419859 2533011558199465044629789)
        ·
          refine ⟨949879334324799391736171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2533011558199465044629789 949879334324799391736171)
          ·
            refine ⟨1424819001487199087604257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949879334324799391736171 1424819001487199087604257)
            ·
              refine ⟨1068614251115399315703193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424819001487199087604257 1068614251115399315703193)
              ·
                refine ⟨801460688336549486777395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068614251115399315703193 801460688336549486777395)
                ·
                  refine ⟨1202191032504824230166093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801460688336549486777395 1202191032504824230166093)
                  ·
                    refine ⟨450821637189309086312285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202191032504824230166093 450821637189309086312285)
                    ·
                      rfl

theorem cell22_1316958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1316958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316958 prefixEnd_1316958 := by exact prefixLift 1316958
  have htrace : WordTrace (prefixWord ++ tailWord_1316958) baseStart_1316958 baseEnd_1316958 := by
    simpa [prefixWord, tailWord_1316958, baseEnd_1316958] using wordTrace_append hprefix tailTrace_1316958
  have hstable : (prefixWord ++ tailWord_1316958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316958).length < 2 ^ (prefixWord ++ tailWord_1316958).sum := by decide
  have hdescent : baseEnd_1316958 < baseStart_1316958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316965 : List Nat := [1, 3, 1, 3, 2, 4, 2, 2, 4]
def baseStart_1316965 : Nat := 118140960795 + 1316965 * 2 ^ 59
def prefixEnd_1316965 : Nat := 4983230072969 + 3 ^ 40 * 1316965 * 2
def baseEnd_1316965 : Nat := 150274677810787800462421

theorem tailTrace_1316965 : CollatzResearch.WordTrace tailWord_1316965 prefixEnd_1316965 150274677810787800462421 := by
  unfold tailWord_1316965
  simp only [CollatzResearch.WordTrace]
  refine ⟨48033659673868199560336349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32022439782578799706890899 48033659673868199560336349)
  ·
    refine ⟨18012622377700574835126131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48033659673868199560336349 18012622377700574835126131)
    ·
      refine ⟨27018933566550862252689197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18012622377700574835126131 27018933566550862252689197)
      ·
        refine ⟨10132100087456573344758449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27018933566550862252689197 10132100087456573344758449)
        ·
          refine ⟨7599075065592430008568837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10132100087456573344758449 7599075065592430008568837)
          ·
            refine ⟨1424826574798580626606657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7599075065592430008568837 1424826574798580626606657)
            ·
              refine ⟨1068619931098935469954993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424826574798580626606657 1068619931098935469954993)
              ·
                refine ⟨801464948324201602466245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068619931098935469954993 801464948324201602466245)
                ·
                  refine ⟨150274677810787800462421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801464948324201602466245 150274677810787800462421)
                  ·
                    rfl

theorem cell22_1316965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_1316965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316965 prefixEnd_1316965 := by exact prefixLift 1316965
  have htrace : WordTrace (prefixWord ++ tailWord_1316965) baseStart_1316965 baseEnd_1316965 := by
    simpa [prefixWord, tailWord_1316965, baseEnd_1316965] using wordTrace_append hprefix tailTrace_1316965
  have hstable : (prefixWord ++ tailWord_1316965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316965).length < 2 ^ (prefixWord ++ tailWord_1316965).sum := by decide
  have hdescent : baseEnd_1316965 < baseStart_1316965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316976 : List Nat := [2, 1, 1, 1, 5, 4, 1, 7]
def baseStart_1316976 : Nat := 118140960795 + 1316976 * 2 ^ 59
def prefixEnd_1316976 : Nat := 4983230072969 + 3 ^ 40 * 1316976 * 2
def baseEnd_1316976 : Nat := 50091977661907004373581

theorem tailTrace_1316976 : CollatzResearch.WordTrace tailWord_1316976 prefixEnd_1316976 50091977661907004373581 := by
  unfold tailWord_1316976
  simp only [CollatzResearch.WordTrace]
  refine ⟨24017030438414174219493391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32022707251218898959324521 24017030438414174219493391)
  ·
    refine ⟨36025545657621261329240087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24017030438414174219493391 36025545657621261329240087)
    ·
      refine ⟨54038318486431891993860131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36025545657621261329240087 54038318486431891993860131)
      ·
        refine ⟨81057477729647837990790197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54038318486431891993860131 81057477729647837990790197)
        ·
          refine ⟨7599138537154484811636581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81057477729647837990790197 7599138537154484811636581)
          ·
            refine ⟨1424838475716465902181859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7599138537154484811636581 1424838475716465902181859)
            ·
              refine ⟨2137257713574698853272789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424838475716465902181859 2137257713574698853272789)
              ·
                refine ⟨50091977661907004373581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2137257713574698853272789 50091977661907004373581)
                ·
                  rfl

theorem cell22_1316976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 7].length) (baseStart_1316976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316976 prefixEnd_1316976 := by exact prefixLift 1316976
  have htrace : WordTrace (prefixWord ++ tailWord_1316976) baseStart_1316976 baseEnd_1316976 := by
    simpa [prefixWord, tailWord_1316976, baseEnd_1316976] using wordTrace_append hprefix tailTrace_1316976
  have hstable : (prefixWord ++ tailWord_1316976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316976).length < 2 ^ (prefixWord ++ tailWord_1316976).sum := by decide
  have hdescent : baseEnd_1316976 < baseStart_1316976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316993 : List Nat := [1, 2, 4, 2, 3, 1, 3, 6]
def baseStart_1316993 : Nat := 118140960795 + 1316993 * 2 ^ 59
def prefixEnd_1316993 : Nat := 4983230072969 + 3 ^ 40 * 1316993 * 2
def baseEnd_1316993 : Nat := 50092624267175629076353

theorem tailTrace_1316993 : CollatzResearch.WordTrace tailWord_1316993 prefixEnd_1316993 50092624267175629076353 := by
  unfold tailWord_1316993
  simp only [CollatzResearch.WordTrace]
  refine ⟨48034680917766760342355633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32023120611844506894903755 48034680917766760342355633)
  ·
    refine ⟨36026010688325070256766725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48034680917766760342355633 36026010688325070256766725)
    ·
      refine ⟨6754877004060950673143761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36026010688325070256766725 6754877004060950673143761)
      ·
        refine ⟨5066157753045713004857821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6754877004060950673143761 5066157753045713004857821)
        ·
          refine ⟨1899809157392142376821683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5066157753045713004857821 1899809157392142376821683)
          ·
            refine ⟨2849713736088213565232525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899809157392142376821683 2849713736088213565232525)
            ·
              refine ⟨1068642651033080086962197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2849713736088213565232525 1068642651033080086962197)
              ·
                refine ⟨50092624267175629076353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1068642651033080086962197 50092624267175629076353)
                ·
                  rfl

theorem cell22_1316993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 6].length) (baseStart_1316993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1316993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1316993 prefixEnd_1316993 := by exact prefixLift 1316993
  have htrace : WordTrace (prefixWord ++ tailWord_1316993) baseStart_1316993 baseEnd_1316993 := by
    simpa [prefixWord, tailWord_1316993, baseEnd_1316993] using wordTrace_append hprefix tailTrace_1316993
  have hstable : (prefixWord ++ tailWord_1316993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316993).length < 2 ^ (prefixWord ++ tailWord_1316993).sum := by decide
  have hdescent : baseEnd_1316993 < baseStart_1316993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 4, 5]
def baseStart_1317019 : Nat := 118140960795 + 1317019 * 2 ^ 59
def prefixEnd_1317019 : Nat := 4983230072969 + 3 ^ 40 * 1317019 * 2
def baseEnd_1317019 : Nat := 450842518735925260537097

theorem tailTrace_1317019 : CollatzResearch.WordTrace tailWord_1317019 prefixEnd_1317019 450842518735925260537097 := by
  unfold tailWord_1317019
  simp only [CollatzResearch.WordTrace]
  refine ⟨48035629215672566782802111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32023752810448377855201407 48035629215672566782802111)
  ·
    refine ⟨72053443823508850174203167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48035629215672566782802111 72053443823508850174203167)
    ·
      refine ⟨108080165735263275261304751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72053443823508850174203167 108080165735263275261304751)
      ·
        refine ⟨162120248602894912891957127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108080165735263275261304751 162120248602894912891957127)
        ·
          refine ⟨243180372904342369337935691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162120248602894912891957127 243180372904342369337935691)
          ·
            refine ⟨364770559356513554006903537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243180372904342369337935691 364770559356513554006903537)
            ·
              refine ⟨273577919517385165505177653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364770559356513554006903537 273577919517385165505177653)
              ·
                refine ⟨25647929954754859266110405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 273577919517385165505177653 25647929954754859266110405)
                ·
                  refine ⟨4808986866516536112395701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25647929954754859266110405 4808986866516536112395701)
                  ·
                    refine ⟨450842518735925260537097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4808986866516536112395701 450842518735925260537097)
                    ·
                      rfl

theorem cell22_1317019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_1317019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317019 prefixEnd_1317019 := by exact prefixLift 1317019
  have htrace : WordTrace (prefixWord ++ tailWord_1317019) baseStart_1317019 baseEnd_1317019 := by
    simpa [prefixWord, tailWord_1317019, baseEnd_1317019] using wordTrace_append hprefix tailTrace_1317019
  have hstable : (prefixWord ++ tailWord_1317019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317019).length < 2 ^ (prefixWord ++ tailWord_1317019).sum := by decide
  have hdescent : baseEnd_1317019 < baseStart_1317019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317021 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 7]
def baseStart_1317021 : Nat := 118140960795 + 1317021 * 2 ^ 59
def prefixEnd_1317021 : Nat := 4983230072969 + 3 ^ 40 * 1317021 * 2
def baseEnd_1317021 : Nat := 150281067792265973995697

theorem tailTrace_1317021 : CollatzResearch.WordTrace tailWord_1317021 prefixEnd_1317021 150281067792265973995697 := by
  unfold tailWord_1317021
  simp only [CollatzResearch.WordTrace]
  refine ⟨48035702161665321124374917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32023801441110214082916611 48035702161665321124374917)
  ·
    refine ⟨9006694155312247710820297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48035702161665321124374917 9006694155312247710820297)
    ·
      refine ⟨6755020616484185783115223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9006694155312247710820297 6755020616484185783115223)
      ·
        refine ⟨10132530924726278674672835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6755020616484185783115223 10132530924726278674672835)
        ·
          refine ⟨15198796387089418012009253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132530924726278674672835 15198796387089418012009253)
          ·
            refine ⟨2849774322579265877251735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15198796387089418012009253 2849774322579265877251735)
            ·
              refine ⟨4274661483868898815877603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849774322579265877251735 4274661483868898815877603)
              ·
                refine ⟨6411992225803348223816405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4274661483868898815877603 6411992225803348223816405)
                ·
                  refine ⟨150281067792265973995697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6411992225803348223816405 150281067792265973995697)
                  ·
                    rfl

theorem cell22_1317021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_1317021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317021 prefixEnd_1317021 := by exact prefixLift 1317021
  have htrace : WordTrace (prefixWord ++ tailWord_1317021) baseStart_1317021 baseEnd_1317021 := by
    simpa [prefixWord, tailWord_1317021, baseEnd_1317021] using wordTrace_append hprefix tailTrace_1317021
  have hstable : (prefixWord ++ tailWord_1317021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317021).length < 2 ^ (prefixWord ++ tailWord_1317021).sum := by decide
  have hdescent : baseEnd_1317021 < baseStart_1317021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317025 : List Nat := [1, 2, 3, 3, 1, 2, 2, 4, 1, 3]
def baseStart_1317025 : Nat := 118140960795 + 1317025 * 2 ^ 59
def prefixEnd_1317025 : Nat := 4983230072969 + 3 ^ 40 * 1317025 * 2
def baseEnd_1317025 : Nat := 450844572658543244887079

theorem tailTrace_1317025 : CollatzResearch.WordTrace tailWord_1317025 prefixEnd_1317025 450844572658543244887079 := by
  unfold tailWord_1317025
  simp only [CollatzResearch.WordTrace]
  refine ⟨48035848053650829807520529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32023898702433886538347019 48035848053650829807520529)
  ·
    refine ⟨36026886040238122355640397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48035848053650829807520529 36026886040238122355640397)
    ·
      refine ⟨13510082265089295883365149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36026886040238122355640397 13510082265089295883365149)
      ·
        refine ⟨5066280849408485956261931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13510082265089295883365149 5066280849408485956261931)
        ·
          refine ⟨7599421274112728934392897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066280849408485956261931 7599421274112728934392897)
          ·
            refine ⟨5699565955584546700794673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7599421274112728934392897 5699565955584546700794673)
            ·
              refine ⟨4274674466688410025596005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5699565955584546700794673 4274674466688410025596005)
              ·
                refine ⟨801501462504076879799251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4274674466688410025596005 801501462504076879799251)
                ·
                  refine ⟨1202252193756115319698877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801501462504076879799251 1202252193756115319698877)
                  ·
                    refine ⟨450844572658543244887079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202252193756115319698877 450844572658543244887079)
                    ·
                      rfl

theorem cell22_1317025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_1317025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317025 prefixEnd_1317025 := by exact prefixLift 1317025
  have htrace : WordTrace (prefixWord ++ tailWord_1317025) baseStart_1317025 baseEnd_1317025 := by
    simpa [prefixWord, tailWord_1317025, baseEnd_1317025] using wordTrace_append hprefix tailTrace_1317025
  have hstable : (prefixWord ++ tailWord_1317025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317025).length < 2 ^ (prefixWord ++ tailWord_1317025).sum := by decide
  have hdescent : baseEnd_1317025 < baseStart_1317025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317044 : List Nat := [2, 5, 3, 1, 1, 2, 2, 6]
def baseStart_1317044 : Nat := 118140960795 + 1317044 * 2 ^ 59
def prefixEnd_1317044 : Nat := 4983230072969 + 3 ^ 40 * 1317044 * 2
def baseEnd_1317044 : Nat := 50094564082981503184669

theorem tailTrace_1317044 : CollatzResearch.WordTrace tailWord_1317044 prefixEnd_1317044 50094564082981503184669 := by
  unfold tailWord_1317044
  simp only [CollatzResearch.WordTrace]
  refine ⟨24018270520290998026231093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32024360693721330701641457 24018270520290998026231093)
  ·
    refine ⟨2251712861277281064959165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24018270520290998026231093 2251712861277281064959165)
    ·
      refine ⟨844392322978980399359687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2251712861277281064959165 844392322978980399359687)
      ·
        refine ⟨1266588484468470599039531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844392322978980399359687 1266588484468470599039531)
        ·
          refine ⟨1899882726702705898559297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266588484468470599039531 1899882726702705898559297)
          ·
            refine ⟨1424912045027029423919473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899882726702705898559297 1424912045027029423919473)
            ·
              refine ⟨1068684033770272067939605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424912045027029423919473 1068684033770272067939605)
              ·
                refine ⟨50094564082981503184669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1068684033770272067939605 50094564082981503184669)
                ·
                  rfl

theorem cell22_1317044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 6].length) (baseStart_1317044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317044 prefixEnd_1317044 := by exact prefixLift 1317044
  have htrace : WordTrace (prefixWord ++ tailWord_1317044) baseStart_1317044 baseEnd_1317044 := by
    simpa [prefixWord, tailWord_1317044, baseEnd_1317044] using wordTrace_append hprefix tailTrace_1317044
  have hstable : (prefixWord ++ tailWord_1317044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317044).length < 2 ^ (prefixWord ++ tailWord_1317044).sum := by decide
  have hdescent : baseEnd_1317044 < baseStart_1317044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317141 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1317141 : Nat := 118140960795 + 1317141 * 2 ^ 59
def prefixEnd_1317141 : Nat := 4983230072969 + 3 ^ 40 * 1317141 * 2
def baseEnd_1317141 : Nat := 450884281829157608986723

theorem tailTrace_1317141 : CollatzResearch.WordTrace tailWord_1317141 prefixEnd_1317141 450884281829157608986723 := by
  unfold tailWord_1317141
  simp only [CollatzResearch.WordTrace]
  refine ⟨48040078921230581618743277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32026719280820387745828851 48040078921230581618743277)
  ·
    refine ⟨18015029595461468107028729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48040078921230581618743277 18015029595461468107028729)
    ·
      refine ⟨13511272196596101080271547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18015029595461468107028729 13511272196596101080271547)
      ·
        refine ⟨20266908294894151620407321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13511272196596101080271547 20266908294894151620407321)
        ·
          refine ⟨15200181221170613715305491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20266908294894151620407321 15200181221170613715305491)
          ·
            refine ⟨22800271831755920572958237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15200181221170613715305491 22800271831755920572958237)
            ·
              refine ⟨8550101936908470214859339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22800271831755920572958237 8550101936908470214859339)
              ·
                refine ⟨12825152905362705322289009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8550101936908470214859339 12825152905362705322289009)
                ·
                  refine ⟨9618864679022028991716757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12825152905362705322289009 9618864679022028991716757)
                  ·
                    refine ⟨450884281829157608986723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9618864679022028991716757 450884281829157608986723)
                    ·
                      rfl

theorem cell22_1317141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1317141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317141 prefixEnd_1317141 := by exact prefixLift 1317141
  have htrace : WordTrace (prefixWord ++ tailWord_1317141) baseStart_1317141 baseEnd_1317141 := by
    simpa [prefixWord, tailWord_1317141, baseEnd_1317141] using wordTrace_append hprefix tailTrace_1317141
  have hstable : (prefixWord ++ tailWord_1317141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317141).length < 2 ^ (prefixWord ++ tailWord_1317141).sum := by decide
  have hdescent : baseEnd_1317141 < baseStart_1317141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317171 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 1, 7]
def baseStart_1317171 : Nat := 118140960795 + 1317171 * 2 ^ 59
def prefixEnd_1317171 : Nat := 4983230072969 + 3 ^ 40 * 1317171 * 2
def baseEnd_1317171 : Nat := 450894551442247530736631

theorem tailTrace_1317171 : CollatzResearch.WordTrace tailWord_1317171 prefixEnd_1317171 450894551442247530736631 := by
  unfold tailWord_1317171
  simp only [CollatzResearch.WordTrace]
  refine ⟨48041173111121896742335367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32027448740747931161556911 48041173111121896742335367)
  ·
    refine ⟨72061759666682845113503051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48041173111121896742335367 72061759666682845113503051)
    ·
      refine ⟨108092639500024267670254577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72061759666682845113503051 108092639500024267670254577)
      ·
        refine ⟨81069479625018200752690933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108092639500024267670254577 81069479625018200752690933)
        ·
          refine ⟨7600263714845456320564775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81069479625018200752690933 7600263714845456320564775)
          ·
            refine ⟨11400395572268184480847163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7600263714845456320564775 11400395572268184480847163)
            ·
              refine ⟨17100593358402276721270745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11400395572268184480847163 17100593358402276721270745)
              ·
                refine ⟨12825445018801707540953059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17100593358402276721270745 12825445018801707540953059)
                ·
                  refine ⟨19238167528202561311429589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12825445018801707540953059 19238167528202561311429589)
                  ·
                    refine ⟨450894551442247530736631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19238167528202561311429589 450894551442247530736631)
                    ·
                      rfl

theorem cell22_1317171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_1317171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317171 prefixEnd_1317171 := by exact prefixLift 1317171
  have htrace : WordTrace (prefixWord ++ tailWord_1317171) baseStart_1317171 baseEnd_1317171 := by
    simpa [prefixWord, tailWord_1317171, baseEnd_1317171] using wordTrace_append hprefix tailTrace_1317171
  have hstable : (prefixWord ++ tailWord_1317171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317171).length < 2 ^ (prefixWord ++ tailWord_1317171).sum := by decide
  have hdescent : baseEnd_1317171 < baseStart_1317171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317177 : List Nat := [1, 2, 1, 6, 1, 1, 1, 5, 1, 3]
def baseStart_1317177 : Nat := 118140960795 + 1317177 * 2 ^ 59
def prefixEnd_1317177 : Nat := 4983230072969 + 3 ^ 40 * 1317177 * 2
def baseEnd_1317177 : Nat := 450896605364865515086613

theorem tailTrace_1317177 : CollatzResearch.WordTrace tailWord_1317177 prefixEnd_1317177 450896605364865515086613 := by
  unfold tailWord_1317177
  simp only [CollatzResearch.WordTrace]
  refine ⟨48041391949100159767053785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32027594632733439844702523 48041391949100159767053785)
  ·
    refine ⟨36031043961825119825290339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48041391949100159767053785 36031043961825119825290339)
    ·
      refine ⟨54046565942737679737935509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36031043961825119825290339 54046565942737679737935509)
      ·
        refine ⟨2533432778565828737715727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54046565942737679737935509 2533432778565828737715727)
        ·
          refine ⟨3800149167848743106573591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533432778565828737715727 3800149167848743106573591)
          ·
            refine ⟨5700223751773114659860387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800149167848743106573591 5700223751773114659860387)
            ·
              refine ⟨8550335627659671989790581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700223751773114659860387 8550335627659671989790581)
              ·
                refine ⟨801593965093094249042867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8550335627659671989790581 801593965093094249042867)
                ·
                  refine ⟨1202390947639641373564301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801593965093094249042867 1202390947639641373564301)
                  ·
                    refine ⟨450896605364865515086613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202390947639641373564301 450896605364865515086613)
                    ·
                      rfl

theorem cell22_1317177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 3].length) (baseStart_1317177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317177 prefixEnd_1317177 := by exact prefixLift 1317177
  have htrace : WordTrace (prefixWord ++ tailWord_1317177) baseStart_1317177 baseEnd_1317177 := by
    simpa [prefixWord, tailWord_1317177, baseEnd_1317177] using wordTrace_append hprefix tailTrace_1317177
  have hstable : (prefixWord ++ tailWord_1317177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317177).length < 2 ^ (prefixWord ++ tailWord_1317177).sum := by decide
  have hdescent : baseEnd_1317177 < baseStart_1317177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317220 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_1317220 : Nat := 118140960795 + 1317220 * 2 ^ 59
def prefixEnd_1317220 : Nat := 4983230072969 + 3 ^ 40 * 1317220 * 2
def baseEnd_1317220 : Nat := 450911325143627736261481

theorem tailTrace_1317220 : CollatzResearch.WordTrace tailWord_1317220 prefixEnd_1317220 450911325143627736261481 := by
  unfold tailWord_1317220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24021480143972189055434557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32028640191962918740579409 24021480143972189055434557)
  ·
    refine ⟨9008055053989570895787959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24021480143972189055434557 9008055053989570895787959)
    ·
      refine ⟨13512082580984356343681939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9008055053989570895787959 13512082580984356343681939)
      ·
        refine ⟨20268123871476534515522909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13512082580984356343681939 20268123871476534515522909)
        ·
          refine ⟨7600546451803700443321091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20268123871476534515522909 7600546451803700443321091)
          ·
            refine ⟨11400819677705550664981637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7600546451803700443321091 11400819677705550664981637)
            ·
              refine ⟨2137653689569790749684057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11400819677705550664981637 2137653689569790749684057)
              ·
                refine ⟨1603240267177343062263043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137653689569790749684057 1603240267177343062263043)
                ·
                  refine ⟨2404860400766014593394565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603240267177343062263043 2404860400766014593394565)
                  ·
                    refine ⟨450911325143627736261481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2404860400766014593394565 450911325143627736261481)
                    ·
                      rfl

theorem cell22_1317220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_1317220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317220 prefixEnd_1317220 := by exact prefixLift 1317220
  have htrace : WordTrace (prefixWord ++ tailWord_1317220) baseStart_1317220 baseEnd_1317220 := by
    simpa [prefixWord, tailWord_1317220, baseEnd_1317220] using wordTrace_append hprefix tailTrace_1317220
  have hstable : (prefixWord ++ tailWord_1317220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317220).length < 2 ^ (prefixWord ++ tailWord_1317220).sum := by decide
  have hdescent : baseEnd_1317220 < baseStart_1317220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317252 : List Nat := [2, 3, 2, 1, 1, 2, 5, 2, 4]
def baseStart_1317252 : Nat := 118140960795 + 1317252 * 2 ^ 59
def prefixEnd_1317252 : Nat := 4983230072969 + 3 ^ 40 * 1317252 * 2
def baseEnd_1317252 : Nat := 150307426465863439820461

theorem tailTrace_1317252 : CollatzResearch.WordTrace tailWord_1317252 prefixEnd_1317252 150307426465863439820461 := by
  unfold tailWord_1317252
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022063711914223788017005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32029418282552298384022673 24022063711914223788017005)
  ·
    refine ⟨9008273891967833920506377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24022063711914223788017005 9008273891967833920506377)
    ·
      refine ⟨6756205418975875440379783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9008273891967833920506377 6756205418975875440379783)
      ·
        refine ⟨10134308128463813160569675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756205418975875440379783 10134308128463813160569675)
        ·
          refine ⟨15201462192695719740854513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134308128463813160569675 15201462192695719740854513)
          ·
            refine ⟨11401096644521789805640885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15201462192695719740854513 11401096644521789805640885)
            ·
              refine ⟨1068852810423917794278833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11401096644521789805640885 1068852810423917794278833)
              ·
                refine ⟨801639607817938345709125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068852810423917794278833 801639607817938345709125)
                ·
                  refine ⟨150307426465863439820461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801639607817938345709125 150307426465863439820461)
                  ·
                    rfl

theorem cell22_1317252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_1317252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317252 prefixEnd_1317252 := by exact prefixLift 1317252
  have htrace : WordTrace (prefixWord ++ tailWord_1317252) baseStart_1317252 baseEnd_1317252 := by
    simpa [prefixWord, tailWord_1317252, baseEnd_1317252] using wordTrace_append hprefix tailTrace_1317252
  have hstable : (prefixWord ++ tailWord_1317252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317252).length < 2 ^ (prefixWord ++ tailWord_1317252).sum := by decide
  have hdescent : baseEnd_1317252 < baseStart_1317252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317355 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 1, 4]
def baseStart_1317355 : Nat := 118140960795 + 1317355 * 2 ^ 59
def prefixEnd_1317355 : Nat := 4983230072969 + 3 ^ 40 * 1317355 * 2
def baseEnd_1317355 : Nat := 450957538402532384136067

theorem tailTrace_1317355 : CollatzResearch.WordTrace tailWord_1317355 prefixEnd_1317355 450957538402532384136067 := by
  unfold tailWord_1317355
  simp only [CollatzResearch.WordTrace]
  refine ⟨48047884142455296167033519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32031922761636864111355679 48047884142455296167033519)
  ·
    refine ⟨72071826213682944250550279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48047884142455296167033519 72071826213682944250550279)
    ·
      refine ⟨108107739320524416375825419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72071826213682944250550279 108107739320524416375825419)
      ·
        refine ⟨162161608980786624563738129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108107739320524416375825419 162161608980786624563738129)
        ·
          refine ⟨121621206735589968422803597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162161608980786624563738129 121621206735589968422803597)
          ·
            refine ⟨45607952525846238158551349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121621206735589968422803597 45607952525846238158551349)
            ·
              refine ⟨4275745549298084827364189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45607952525846238158551349 4275745549298084827364189)
              ·
                refine ⟨1603404580986781810261571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4275745549298084827364189 1603404580986781810261571)
                ·
                  refine ⟨2405106871480172715392357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603404580986781810261571 2405106871480172715392357)
                  ·
                    refine ⟨450957538402532384136067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405106871480172715392357 450957538402532384136067)
                    ·
                      rfl

theorem cell22_1317355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 4].length) (baseStart_1317355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317355 prefixEnd_1317355 := by exact prefixLift 1317355
  have htrace : WordTrace (prefixWord ++ tailWord_1317355) baseStart_1317355 baseEnd_1317355 := by
    simpa [prefixWord, tailWord_1317355, baseEnd_1317355] using wordTrace_append hprefix tailTrace_1317355
  have hstable : (prefixWord ++ tailWord_1317355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317355).length < 2 ^ (prefixWord ++ tailWord_1317355).sum := by decide
  have hdescent : baseEnd_1317355 < baseStart_1317355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317400 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_1317400 : Nat := 118140960795 + 1317400 * 2 ^ 59
def prefixEnd_1317400 : Nat := 4983230072969 + 3 ^ 40 * 1317400 * 2
def baseEnd_1317400 : Nat := 450972942822167266760929

theorem tailTrace_1317400 : CollatzResearch.WordTrace tailWord_1317400 prefixEnd_1317400 450972942822167266760929 := by
  unfold tailWord_1317400
  simp only [CollatzResearch.WordTrace]
  refine ⟨24024762713646134426210827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32033016951528179234947769 24024762713646134426210827)
  ·
    refine ⟨36037144070469201639316241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24024762713646134426210827 36037144070469201639316241)
    ·
      refine ⟨27027858052851901229487181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36037144070469201639316241 27027858052851901229487181)
      ·
        refine ⟨10135446769819462961057693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27027858052851901229487181 10135446769819462961057693)
        ·
          refine ⟨3800792538682298610396635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10135446769819462961057693 3800792538682298610396635)
          ·
            refine ⟨5701188808023447915594953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800792538682298610396635 5701188808023447915594953)
            ·
              refine ⟨4275891606017585936696215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701188808023447915594953 4275891606017585936696215)
              ·
                refine ⟨6413837409026378905044323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275891606017585936696215 6413837409026378905044323)
                ·
                  refine ⟨9620756113539568357566485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413837409026378905044323 9620756113539568357566485)
                  ·
                    refine ⟨450972942822167266760929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9620756113539568357566485 450972942822167266760929)
                    ·
                      rfl

theorem cell22_1317400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_1317400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317400 prefixEnd_1317400 := by exact prefixLift 1317400
  have htrace : WordTrace (prefixWord ++ tailWord_1317400) baseStart_1317400 baseEnd_1317400 := by
    simpa [prefixWord, tailWord_1317400, baseEnd_1317400] using wordTrace_append hprefix tailTrace_1317400
  have hstable : (prefixWord ++ tailWord_1317400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317400).length < 2 ^ (prefixWord ++ tailWord_1317400).sum := by decide
  have hdescent : baseEnd_1317400 < baseStart_1317400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317404 : List Nat := [2, 2, 3, 1, 2, 4, 1, 3, 4]
def baseStart_1317404 : Nat := 118140960795 + 1317404 * 2 ^ 59
def prefixEnd_1317404 : Nat := 4983230072969 + 3 ^ 40 * 1317404 * 2
def baseEnd_1317404 : Nat := 150324770701304196553639

theorem tailTrace_1317404 : CollatzResearch.WordTrace tailWord_1317404 prefixEnd_1317404 150324770701304196553639 := by
  unfold tailWord_1317404
  simp only [CollatzResearch.WordTrace]
  refine ⟨24024835659638888767783633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32033114212851851690378177 24024835659638888767783633)
  ·
    refine ⟨18018626744729166575837725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24024835659638888767783633 18018626744729166575837725)
    ·
      refine ⟨6756985029273437465939147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18018626744729166575837725 6756985029273437465939147)
      ·
        refine ⟨10135477543910156198908721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756985029273437465939147 10135477543910156198908721)
        ·
          refine ⟨7601608157932617149181541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10135477543910156198908721 7601608157932617149181541)
          ·
            refine ⟨1425301529612365715471539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7601608157932617149181541 1425301529612365715471539)
            ·
              refine ⟨2137952294418548573207309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425301529612365715471539 2137952294418548573207309)
              ·
                refine ⟨801732110406955714952741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137952294418548573207309 801732110406955714952741)
                ·
                  refine ⟨150324770701304196553639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801732110406955714952741 150324770701304196553639)
                  ·
                    rfl

theorem cell22_1317404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_1317404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317404 prefixEnd_1317404 := by exact prefixLift 1317404
  have htrace : WordTrace (prefixWord ++ tailWord_1317404) baseStart_1317404 baseEnd_1317404 := by
    simpa [prefixWord, tailWord_1317404, baseEnd_1317404] using wordTrace_append hprefix tailTrace_1317404
  have hstable : (prefixWord ++ tailWord_1317404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317404).length < 2 ^ (prefixWord ++ tailWord_1317404).sum := by decide
  have hdescent : baseEnd_1317404 < baseStart_1317404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317436 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_1317436 : Nat := 118140960795 + 1317436 * 2 ^ 59
def prefixEnd_1317436 : Nat := 4983230072969 + 3 ^ 40 * 1317436 * 2
def baseEnd_1317436 : Nat := 450985266357875172860819

theorem tailTrace_1317436 : CollatzResearch.WordTrace tailWord_1317436 prefixEnd_1317436 450985266357875172860819 := by
  unfold tailWord_1317436
  simp only [CollatzResearch.WordTrace]
  refine ⟨24025419227580923500366081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32033892303441231333821441 24025419227580923500366081)
  ·
    refine ⟨18019064420685692625274561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24025419227580923500366081 18019064420685692625274561)
    ·
      refine ⟨13514298315514269468955921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18019064420685692625274561 13514298315514269468955921)
      ·
        refine ⟨10135723736635702101716941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13514298315514269468955921 10135723736635702101716941)
        ·
          refine ⟨3800896401238388288143853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10135723736635702101716941 3800896401238388288143853)
          ·
            refine ⟨1425336150464395608053945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3800896401238388288143853 1425336150464395608053945)
            ·
              refine ⟨1069002112848296706040459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425336150464395608053945 1069002112848296706040459)
              ·
                refine ⟨1603503169272445059060689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069002112848296706040459 1603503169272445059060689)
                ·
                  refine ⟨1202627376954333794295517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1603503169272445059060689 1202627376954333794295517)
                  ·
                    refine ⟨450985266357875172860819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202627376954333794295517 450985266357875172860819)
                    ·
                      rfl

theorem cell22_1317436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_1317436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317436 prefixEnd_1317436 := by exact prefixLift 1317436
  have htrace : WordTrace (prefixWord ++ tailWord_1317436) baseStart_1317436 baseEnd_1317436 := by
    simpa [prefixWord, tailWord_1317436, baseEnd_1317436] using wordTrace_append hprefix tailTrace_1317436
  have hstable : (prefixWord ++ tailWord_1317436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317436).length < 2 ^ (prefixWord ++ tailWord_1317436).sum := by decide
  have hdescent : baseEnd_1317436 < baseStart_1317436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317470 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1317470 : Nat := 118140960795 + 1317470 * 2 ^ 59
def prefixEnd_1317470 : Nat := 4983230072969 + 3 ^ 40 * 1317470 * 2
def baseEnd_1317470 : Nat := 450996905252710417510715

theorem tailTrace_1317470 : CollatzResearch.WordTrace tailWord_1317470 prefixEnd_1317470 450996905252710417510715 := by
  unfold tailWord_1317470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006509817129833850933733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32034719024692447204979909 6006509817129833850933733)
  ·
    refine ⟨1126220590711843847050075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6006509817129833850933733 1126220590711843847050075)
    ·
      refine ⟨1689330886067765770575113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126220590711843847050075 1689330886067765770575113)
      ·
        refine ⟨1266998164550824327931335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689330886067765770575113 1266998164550824327931335)
        ·
          refine ⟨1900497246826236491897003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266998164550824327931335 1900497246826236491897003)
          ·
            refine ⟨2850745870239354737845505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900497246826236491897003 2850745870239354737845505)
            ·
              refine ⟨2138059402679516053384129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850745870239354737845505 2138059402679516053384129)
              ·
                refine ⟨1603544552009637040038097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138059402679516053384129 1603544552009637040038097)
                ·
                  refine ⟨1202658414007227780028573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1603544552009637040038097 1202658414007227780028573)
                  ·
                    refine ⟨450996905252710417510715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202658414007227780028573 450996905252710417510715)
                    ·
                      rfl

theorem cell22_1317470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1317470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317470 prefixEnd_1317470 := by exact prefixLift 1317470
  have htrace : WordTrace (prefixWord ++ tailWord_1317470) baseStart_1317470 baseEnd_1317470 := by
    simpa [prefixWord, tailWord_1317470, baseEnd_1317470] using wordTrace_append hprefix tailTrace_1317470
  have hstable : (prefixWord ++ tailWord_1317470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317470).length < 2 ^ (prefixWord ++ tailWord_1317470).sum := by decide
  have hdescent : baseEnd_1317470 < baseStart_1317470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317475 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 2, 5]
def baseStart_1317475 : Nat := 118140960795 + 1317475 * 2 ^ 59
def prefixEnd_1317475 : Nat := 4983230072969 + 3 ^ 40 * 1317475 * 2
def baseEnd_1317475 : Nat := 450998616854892071135699

theorem tailTrace_1317475 : CollatzResearch.WordTrace tailWord_1317475 prefixEnd_1317475 450998616854892071135699 := by
  unfold tailWord_1317475
  simp only [CollatzResearch.WordTrace]
  refine ⟨48052260902020556661401879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32034840601347037774267919 48052260902020556661401879)
  ·
    refine ⟨72078391353030834992102819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48052260902020556661401879 72078391353030834992102819)
    ·
      refine ⟨108117587029546252488154229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72078391353030834992102819 108117587029546252488154229)
      ·
        refine ⟨10136023784019961170764459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108117587029546252488154229 10136023784019961170764459)
        ·
          refine ⟨15204035676029941756146689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10136023784019961170764459 15204035676029941756146689)
          ·
            refine ⟨11403026757022456317110017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15204035676029941756146689 11403026757022456317110017)
            ·
              refine ⟨8552270067766842237832513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11403026757022456317110017 8552270067766842237832513)
              ·
                refine ⟨6414202550825131678374385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8552270067766842237832513 6414202550825131678374385)
                ·
                  refine ⟨4810651913118848758780789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414202550825131678374385 4810651913118848758780789)
                  ·
                    refine ⟨450998616854892071135699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4810651913118848758780789 450998616854892071135699)
                    ·
                      rfl

theorem cell22_1317475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_1317475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317475 prefixEnd_1317475 := by exact prefixLift 1317475
  have htrace : WordTrace (prefixWord ++ tailWord_1317475) baseStart_1317475 baseEnd_1317475 := by
    simpa [prefixWord, tailWord_1317475, baseEnd_1317475] using wordTrace_append hprefix tailTrace_1317475
  have hstable : (prefixWord ++ tailWord_1317475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317475).length < 2 ^ (prefixWord ++ tailWord_1317475).sum := by decide
  have hdescent : baseEnd_1317475 < baseStart_1317475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317558 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1317558 : Nat := 118140960795 + 1317558 * 2 ^ 59
def prefixEnd_1317558 : Nat := 4983230072969 + 3 ^ 40 * 1317558 * 2
def baseEnd_1317558 : Nat := 451027029451107521310445

theorem tailTrace_1317558 : CollatzResearch.WordTrace tailWord_1317558 prefixEnd_1317558 451027029451107521310445 := by
  unfold tailWord_1317558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003455510044991364792083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32036858773813241224448885 3003455510044991364792083)
  ·
    refine ⟨4505183265067487047188125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3003455510044991364792083 4505183265067487047188125)
    ·
      refine ⟨1689443724400307642695547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4505183265067487047188125 1689443724400307642695547)
      ·
        refine ⟨2534165586600461464043321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689443724400307642695547 2534165586600461464043321)
        ·
          refine ⟨1900624189950346098032491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2534165586600461464043321 1900624189950346098032491)
          ·
            refine ⟨2850936284925519147048737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900624189950346098032491 2850936284925519147048737)
            ·
              refine ⟨2138202213694139360286553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850936284925519147048737 2138202213694139360286553)
              ·
                refine ⟨1603651660270604520214915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138202213694139360286553 1603651660270604520214915)
                ·
                  refine ⟨2405477490405906780322373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603651660270604520214915 2405477490405906780322373)
                  ·
                    refine ⟨451027029451107521310445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2405477490405906780322373 451027029451107521310445)
                    ·
                      rfl

theorem cell22_1317558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1317558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317558 prefixEnd_1317558 := by exact prefixLift 1317558
  have htrace : WordTrace (prefixWord ++ tailWord_1317558) baseStart_1317558 baseEnd_1317558 := by
    simpa [prefixWord, tailWord_1317558, baseEnd_1317558] using wordTrace_append hprefix tailTrace_1317558
  have hstable : (prefixWord ++ tailWord_1317558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317558).length < 2 ^ (prefixWord ++ tailWord_1317558).sum := by decide
  have hdescent : baseEnd_1317558 < baseStart_1317558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317567 : List Nat := [1, 1, 2, 2, 2, 4, 4, 6]
def baseStart_1317567 : Nat := 118140960795 + 1317567 * 2 ^ 59
def prefixEnd_1317567 : Nat := 4983230072969 + 3 ^ 40 * 1317567 * 2
def baseEnd_1317567 : Nat := 50114456703892721981713

theorem tailTrace_1317567 : CollatzResearch.WordTrace tailWord_1317567 prefixEnd_1317567 50114456703892721981713 := by
  unfold tailWord_1317567
  simp only [CollatzResearch.WordTrace]
  refine ⟨48055616417687256373750955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32037077611791504249167303 48055616417687256373750955)
  ·
    refine ⟨72083424626530884560626433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48055616417687256373750955 72083424626530884560626433)
    ·
      refine ⟨54062568469898163420469825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72083424626530884560626433 54062568469898163420469825)
      ·
        refine ⟨40546926352423622565352369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54062568469898163420469825 40546926352423622565352369)
        ·
          refine ⟨30410194764317716924014277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40546926352423622565352369 30410194764317716924014277)
          ·
            refine ⟨5701911518309571923252677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30410194764317716924014277 5701911518309571923252677)
            ·
              refine ⟨1069108409683044735609877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5701911518309571923252677 1069108409683044735609877)
              ·
                refine ⟨50114456703892721981713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1069108409683044735609877 50114456703892721981713)
                ·
                  rfl

theorem cell22_1317567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 6].length) (baseStart_1317567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317567 prefixEnd_1317567 := by exact prefixLift 1317567
  have htrace : WordTrace (prefixWord ++ tailWord_1317567) baseStart_1317567 baseEnd_1317567 := by
    simpa [prefixWord, tailWord_1317567, baseEnd_1317567] using wordTrace_append hprefix tailTrace_1317567
  have hstable : (prefixWord ++ tailWord_1317567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317567).length < 2 ^ (prefixWord ++ tailWord_1317567).sum := by decide
  have hdescent : baseEnd_1317567 < baseStart_1317567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317599 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 3, 3]
def baseStart_1317599 : Nat := 118140960795 + 1317599 * 2 ^ 59
def prefixEnd_1317599 : Nat := 4983230072969 + 3 ^ 40 * 1317599 * 2
def baseEnd_1317599 : Nat := 451041064588997081035319

theorem tailTrace_1317599 : CollatzResearch.WordTrace tailWord_1317599 prefixEnd_1317599 451041064588997081035319 := by
  unfold tailWord_1317599
  simp only [CollatzResearch.WordTrace]
  refine ⟨48056783553571325838915851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32037855702380883892610567 48056783553571325838915851)
  ·
    refine ⟨72085175330356988758373777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48056783553571325838915851 72085175330356988758373777)
    ·
      refine ⟨54063881497767741568780333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72085175330356988758373777 54063881497767741568780333)
      ·
        refine ⟨20273955561662903088292625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54063881497767741568780333 20273955561662903088292625)
        ·
          refine ⟨15205466671247177316219469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20273955561662903088292625 15205466671247177316219469)
          ·
            refine ⟨5702050001717691493582301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15205466671247177316219469 5702050001717691493582301)
            ·
              refine ⟨2138268750644134310093363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5702050001717691493582301 2138268750644134310093363)
              ·
                refine ⟨3207403125966201465140045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138268750644134310093363 3207403125966201465140045)
                ·
                  refine ⟨1202776172237325549427517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3207403125966201465140045 1202776172237325549427517)
                  ·
                    refine ⟨451041064588997081035319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202776172237325549427517 451041064588997081035319)
                    ·
                      rfl

theorem cell22_1317599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_1317599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317599 prefixEnd_1317599 := by exact prefixLift 1317599
  have htrace : WordTrace (prefixWord ++ tailWord_1317599) baseStart_1317599 baseEnd_1317599 := by
    simpa [prefixWord, tailWord_1317599, baseEnd_1317599] using wordTrace_append hprefix tailTrace_1317599
  have hstable : (prefixWord ++ tailWord_1317599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317599).length < 2 ^ (prefixWord ++ tailWord_1317599).sum := by decide
  have hdescent : baseEnd_1317599 < baseStart_1317599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317650 : List Nat := [3, 2, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1317650 : Nat := 118140960795 + 1317650 * 2 ^ 59
def prefixEnd_1317650 : Nat := 4983230072969 + 3 ^ 40 * 1317650 * 2
def baseEnd_1317650 : Nat := 451058522931249948010163

theorem tailTrace_1317650 : CollatzResearch.WordTrace tailWord_1317650 prefixEnd_1317650 451058522931249948010163 := by
  unfold tailWord_1317650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12014660919096640387255601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32039095784257707699348269 12014660919096640387255601)
  ·
    refine ⟨9010995689322480290441701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12014660919096640387255601 9010995689322480290441701)
    ·
      refine ⟨1689561691747965054457819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9010995689322480290441701 1689561691747965054457819)
      ·
        refine ⟨2534342537621947581686729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689561691747965054457819 2534342537621947581686729)
        ·
          refine ⟨1900756903216460686265047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2534342537621947581686729 1900756903216460686265047)
          ·
            refine ⟨2851135354824691029397571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900756903216460686265047 2851135354824691029397571)
            ·
              refine ⟨4276703032237036544096357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2851135354824691029397571 4276703032237036544096357)
              ·
                refine ⟨801881818544444352018067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4276703032237036544096357 801881818544444352018067)
                ·
                  refine ⟨1202822727816666528027101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801881818544444352018067 1202822727816666528027101)
                  ·
                    refine ⟨451058522931249948010163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202822727816666528027101 451058522931249948010163)
                    ·
                      rfl

theorem cell22_1317650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1317650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317650 prefixEnd_1317650 := by exact prefixLift 1317650
  have htrace : WordTrace (prefixWord ++ tailWord_1317650) baseStart_1317650 baseEnd_1317650 := by
    simpa [prefixWord, tailWord_1317650, baseEnd_1317650] using wordTrace_append hprefix tailTrace_1317650
  have hstable : (prefixWord ++ tailWord_1317650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317650).length < 2 ^ (prefixWord ++ tailWord_1317650).sum := by decide
  have hdescent : baseEnd_1317650 < baseStart_1317650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317661 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1317661 : Nat := 118140960795 + 1317661 * 2 ^ 59
def prefixEnd_1317661 : Nat := 4983230072969 + 3 ^ 40 * 1317661 * 2
def baseEnd_1317661 : Nat := 451062288456049585985129

theorem tailTrace_1317661 : CollatzResearch.WordTrace tailWord_1317661 prefixEnd_1317661 451062288456049585985129 := by
  unfold tailWord_1317661
  simp only [CollatzResearch.WordTrace]
  refine ⟨48059044879346710427672837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32039363252897806951781891 48059044879346710427672837)
  ·
    refine ⟨9011070914877508205188657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48059044879346710427672837 9011070914877508205188657)
    ·
      refine ⟨6758303186158131153891493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9011070914877508205188657 6758303186158131153891493)
      ·
        refine ⟨1267181847404649591354655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6758303186158131153891493 1267181847404649591354655)
        ·
          refine ⟨1900772771106974387031983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267181847404649591354655 1900772771106974387031983)
          ·
            refine ⟨2851159156660461580547975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900772771106974387031983 2851159156660461580547975)
            ·
              refine ⟨4276738734990692370821963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2851159156660461580547975 4276738734990692370821963)
              ·
                refine ⟨6415108102486038556232945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276738734990692370821963 6415108102486038556232945)
                ·
                  refine ⟨4811331076864528917174709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6415108102486038556232945 4811331076864528917174709)
                  ·
                    refine ⟨451062288456049585985129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4811331076864528917174709 451062288456049585985129)
                    ·
                      rfl

theorem cell22_1317661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1317661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317661 prefixEnd_1317661 := by exact prefixLift 1317661
  have htrace : WordTrace (prefixWord ++ tailWord_1317661) baseStart_1317661 baseEnd_1317661 := by
    simpa [prefixWord, tailWord_1317661, baseEnd_1317661] using wordTrace_append hprefix tailTrace_1317661
  have hstable : (prefixWord ++ tailWord_1317661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317661).length < 2 ^ (prefixWord ++ tailWord_1317661).sum := by decide
  have hdescent : baseEnd_1317661 < baseStart_1317661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317687 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 1, 6]
def baseStart_1317687 : Nat := 118140960795 + 1317687 * 2 ^ 59
def prefixEnd_1317687 : Nat := 4983230072969 + 3 ^ 40 * 1317687 * 2
def baseEnd_1317687 : Nat := 451071188787394184835049

theorem tailTrace_1317687 : CollatzResearch.WordTrace tailWord_1317687 prefixEnd_1317687 451071188787394184835049 := by
  unfold tailWord_1317687
  simp only [CollatzResearch.WordTrace]
  refine ⟨48059993177252516868119315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32039995451501677912079543 48059993177252516868119315)
  ·
    refine ⟨72089989765878775302178973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48059993177252516868119315 72089989765878775302178973)
    ·
      refine ⟨27033746162204540738317115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72089989765878775302178973 27033746162204540738317115)
      ·
        refine ⟨40550619243306811107475673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27033746162204540738317115 40550619243306811107475673)
        ·
          refine ⟨30412964432480108330606755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40550619243306811107475673 30412964432480108330606755)
          ·
            refine ⟨45619446648720162495910133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30412964432480108330606755 45619446648720162495910133)
            ·
              refine ⟨4276823123317515233991575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45619446648720162495910133 4276823123317515233991575)
              ·
                refine ⟨6415234684976272850987363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276823123317515233991575 6415234684976272850987363)
                ·
                  refine ⟨9622852027464409276481045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6415234684976272850987363 9622852027464409276481045)
                  ·
                    refine ⟨451071188787394184835049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9622852027464409276481045 451071188787394184835049)
                    ·
                      rfl

theorem cell22_1317687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_1317687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317687 prefixEnd_1317687 := by exact prefixLift 1317687
  have htrace : WordTrace (prefixWord ++ tailWord_1317687) baseStart_1317687 baseEnd_1317687 := by
    simpa [prefixWord, tailWord_1317687, baseEnd_1317687] using wordTrace_append hprefix tailTrace_1317687
  have hstable : (prefixWord ++ tailWord_1317687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317687).length < 2 ^ (prefixWord ++ tailWord_1317687).sum := by decide
  have hdescent : baseEnd_1317687 < baseStart_1317687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317736 : List Nat := [2, 1, 4, 2, 1, 4, 2, 6]
def baseStart_1317736 : Nat := 118140960795 + 1317736 * 2 ^ 59
def prefixEnd_1317736 : Nat := 4983230072969 + 3 ^ 40 * 1317736 * 2
def baseEnd_1317736 : Nat := 50120884720974932262211

theorem tailTrace_1317736 : CollatzResearch.WordTrace tailWord_1317736 prefixEnd_1317736 50120884720974932262211 := by
  unfold tailWord_1317736
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030890177037499118326531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32041186902716665491102041 24030890177037499118326531)
  ·
    refine ⟨36046335265556248677489797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24030890177037499118326531 36046335265556248677489797)
    ·
      refine ⟨6758687862291796627029337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36046335265556248677489797 6758687862291796627029337)
      ·
        refine ⟨5069015896718847470272003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6758687862291796627029337 5069015896718847470272003)
        ·
          refine ⟨7603523845078271205408005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5069015896718847470272003 7603523845078271205408005)
          ·
            refine ⟨1425660720952175851014001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7603523845078271205408005 1425660720952175851014001)
            ·
              refine ⟨1069245540714131888260501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425660720952175851014001 1069245540714131888260501)
              ·
                refine ⟨50120884720974932262211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1069245540714131888260501 50120884720974932262211)
                ·
                  rfl

theorem cell22_1317736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 6].length) (baseStart_1317736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317736 prefixEnd_1317736 := by exact prefixLift 1317736
  have htrace : WordTrace (prefixWord ++ tailWord_1317736) baseStart_1317736 baseEnd_1317736 := by
    simpa [prefixWord, tailWord_1317736, baseEnd_1317736] using wordTrace_append hprefix tailTrace_1317736
  have hstable : (prefixWord ++ tailWord_1317736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317736).length < 2 ^ (prefixWord ++ tailWord_1317736).sum := by decide
  have hdescent : baseEnd_1317736 < baseStart_1317736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317747 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 7]
def baseStart_1317747 : Nat := 118140960795 + 1317747 * 2 ^ 59
def prefixEnd_1317747 : Nat := 4983230072969 + 3 ^ 40 * 1317747 * 2
def baseEnd_1317747 : Nat := 150363909337858009444955

theorem tailTrace_1317747 : CollatzResearch.WordTrace tailWord_1317747 prefixEnd_1317747 150363909337858009444955 := by
  unfold tailWord_1317747
  simp only [CollatzResearch.WordTrace]
  refine ⟨48062181557035147115303495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32041454371356764743535663 48062181557035147115303495)
  ·
    refine ⟨72093272335552720672955243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48062181557035147115303495 72093272335552720672955243)
    ·
      refine ⟨108139908503329081009432865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72093272335552720672955243 108139908503329081009432865)
      ·
        refine ⟨81104931377496810757074649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108139908503329081009432865 81104931377496810757074649)
        ·
          refine ⟨60828698533122608067805987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81104931377496810757074649 60828698533122608067805987)
          ·
            refine ⟨91243047799683912101708981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60828698533122608067805987 91243047799683912101708981)
            ·
              refine ⟨8554035731220366759535217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91243047799683912101708981 8554035731220366759535217)
              ·
                refine ⟨6415526798415275069651413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8554035731220366759535217 6415526798415275069651413)
                ·
                  refine ⟨150363909337858009444955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6415526798415275069651413 150363909337858009444955)
                  ·
                    rfl

theorem cell22_1317747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_1317747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317747 prefixEnd_1317747 := by exact prefixLift 1317747
  have htrace : WordTrace (prefixWord ++ tailWord_1317747) baseStart_1317747 baseEnd_1317747 := by
    simpa [prefixWord, tailWord_1317747, baseEnd_1317747] using wordTrace_append hprefix tailTrace_1317747
  have hstable : (prefixWord ++ tailWord_1317747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317747).length < 2 ^ (prefixWord ++ tailWord_1317747).sum := by decide
  have hdescent : baseEnd_1317747 < baseStart_1317747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317764 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1317764 : Nat := 118140960795 + 1317764 * 2 ^ 59
def prefixEnd_1317764 : Nat := 4983230072969 + 3 ^ 40 * 1317764 * 2
def baseEnd_1317764 : Nat := 150365849153663883553271

theorem tailTrace_1317764 : CollatzResearch.WordTrace tailWord_1317764 prefixEnd_1317764 150365849153663883553271 := by
  unfold tailWord_1317764
  simp only [CollatzResearch.WordTrace]
  refine ⟨24031400798986779509336173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32041867731982372679114897 24031400798986779509336173)
  ·
    refine ⟨9011775299620042316001065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24031400798986779509336173 9011775299620042316001065)
    ·
      refine ⟨6758831474715031737000799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9011775299620042316001065 6758831474715031737000799)
      ·
        refine ⟨10138247212072547605501199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758831474715031737000799 10138247212072547605501199)
        ·
          refine ⟨15207370818108821408251799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10138247212072547605501199 15207370818108821408251799)
          ·
            refine ⟨22811056227163232112377699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15207370818108821408251799 22811056227163232112377699)
            ·
              refine ⟨34216584340744848168566549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22811056227163232112377699 34216584340744848168566549)
              ·
                refine ⟨1603902390972414757901557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34216584340744848168566549 1603902390972414757901557)
                ·
                  refine ⟨150365849153663883553271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1603902390972414757901557 150365849153663883553271)
                  ·
                    rfl

theorem cell22_1317764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1317764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317764 prefixEnd_1317764 := by exact prefixLift 1317764
  have htrace : WordTrace (prefixWord ++ tailWord_1317764) baseStart_1317764 baseEnd_1317764 := by
    simpa [prefixWord, tailWord_1317764, baseEnd_1317764] using wordTrace_append hprefix tailTrace_1317764
  have hstable : (prefixWord ++ tailWord_1317764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317764).length < 2 ^ (prefixWord ++ tailWord_1317764).sum := by decide
  have hdescent : baseEnd_1317764 < baseStart_1317764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317768 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1317768 : Nat := 118140960795 + 1317768 * 2 ^ 59
def prefixEnd_1317768 : Nat := 4983230072969 + 3 ^ 40 * 1317768 * 2
def baseEnd_1317768 : Nat := 451098916742736973559801

theorem tailTrace_1317768 : CollatzResearch.WordTrace tailWord_1317768 prefixEnd_1317768 451098916742736973559801 := by
  unfold tailWord_1317768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24031473744979533850908979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32041964993306045134545305 24031473744979533850908979)
  ·
    refine ⟨36047210617469300776363469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24031473744979533850908979 36047210617469300776363469)
    ·
      refine ⟨13517703981550987791136301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36047210617469300776363469 13517703981550987791136301)
      ·
        refine ⟨5069138993081620421676113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13517703981550987791136301 5069138993081620421676113)
        ·
          refine ⟨3801854244811215316257085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5069138993081620421676113 3801854244811215316257085)
          ·
            refine ⟨1425695341804205743596407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3801854244811215316257085 1425695341804205743596407)
            ·
              refine ⟨2138543012706308615394611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425695341804205743596407 2138543012706308615394611)
              ·
                refine ⟨3207814519059462923091917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138543012706308615394611 3207814519059462923091917)
                ·
                  refine ⟨1202930444647298596159469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3207814519059462923091917 1202930444647298596159469)
                  ·
                    refine ⟨451098916742736973559801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202930444647298596159469 451098916742736973559801)
                    ·
                      rfl

theorem cell22_1317768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1317768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317768 prefixEnd_1317768 := by exact prefixLift 1317768
  have htrace : WordTrace (prefixWord ++ tailWord_1317768) baseStart_1317768 baseEnd_1317768 := by
    simpa [prefixWord, tailWord_1317768, baseEnd_1317768] using wordTrace_append hprefix tailTrace_1317768
  have hstable : (prefixWord ++ tailWord_1317768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317768).length < 2 ^ (prefixWord ++ tailWord_1317768).sum := by decide
  have hdescent : baseEnd_1317768 < baseStart_1317768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317777 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1317777 : Nat := 118140960795 + 1317777 * 2 ^ 59
def prefixEnd_1317777 : Nat := 4983230072969 + 3 ^ 40 * 1317777 * 2
def baseEnd_1317777 : Nat := 451101997626663950084773

theorem tailTrace_1317777 : CollatzResearch.WordTrace tailWord_1317777 prefixEnd_1317777 451101997626663950084773 := by
  unfold tailWord_1317777
  simp only [CollatzResearch.WordTrace]
  refine ⟨48063275746926462238895585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32042183831284308159263723 48063275746926462238895585)
  ·
    refine ⟨36047456810194846679171689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48063275746926462238895585 36047456810194846679171689)
    ·
      refine ⟨27035592607646135009378767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36047456810194846679171689 27035592607646135009378767)
      ·
        refine ⟨40553388911469202514068151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27035592607646135009378767 40553388911469202514068151)
        ·
          refine ⟨60830083367203803771102227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40553388911469202514068151 60830083367203803771102227)
          ·
            refine ⟨91245125050805705656653341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60830083367203803771102227 91245125050805705656653341)
            ·
              refine ⟨34216921894052139621245003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91245125050805705656653341 34216921894052139621245003)
              ·
                refine ⟨51325382841078209431867505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34216921894052139621245003 51325382841078209431867505)
                ·
                  refine ⟨38494037130808657073900629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51325382841078209431867505 38494037130808657073900629)
                  ·
                    refine ⟨451101997626663950084773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38494037130808657073900629 451101997626663950084773)
                    ·
                      rfl

theorem cell22_1317777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1317777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317777 prefixEnd_1317777 := by exact prefixLift 1317777
  have htrace : WordTrace (prefixWord ++ tailWord_1317777) baseStart_1317777 baseEnd_1317777 := by
    simpa [prefixWord, tailWord_1317777, baseEnd_1317777] using wordTrace_append hprefix tailTrace_1317777
  have hstable : (prefixWord ++ tailWord_1317777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317777).length < 2 ^ (prefixWord ++ tailWord_1317777).sum := by decide
  have hdescent : baseEnd_1317777 < baseStart_1317777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317781 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 5]
def baseStart_1317781 : Nat := 118140960795 + 1317781 * 2 ^ 59
def prefixEnd_1317781 : Nat := 4983230072969 + 3 ^ 40 * 1317781 * 2
def baseEnd_1317781 : Nat := 150367788969469757661587

theorem tailTrace_1317781 : CollatzResearch.WordTrace tailWord_1317781 prefixEnd_1317781 150367788969469757661587 := by
  unfold tailWord_1317781
  simp only [CollatzResearch.WordTrace]
  refine ⟨48063421638911970922041197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32042281092607980614694131 48063421638911970922041197)
  ·
    refine ⟨18023783114591989095765449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48063421638911970922041197 18023783114591989095765449)
    ·
      refine ⟨13517837335943991821824087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18023783114591989095765449 13517837335943991821824087)
      ·
        refine ⟨20276756003915987732736131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13517837335943991821824087 20276756003915987732736131)
        ·
          refine ⟨30415134005873981599104197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20276756003915987732736131 30415134005873981599104197)
          ·
            refine ⟨5702837626101371549832037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30415134005873981599104197 5702837626101371549832037)
            ·
              refine ⟨1069282054894007165593507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5702837626101371549832037 1069282054894007165593507)
              ·
                refine ⟨1603923082341010748390261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069282054894007165593507 1603923082341010748390261)
                ·
                  refine ⟨150367788969469757661587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1603923082341010748390261 150367788969469757661587)
                  ·
                    rfl

theorem cell22_1317781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_1317781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317781 prefixEnd_1317781 := by exact prefixLift 1317781
  have htrace : WordTrace (prefixWord ++ tailWord_1317781) baseStart_1317781 baseEnd_1317781 := by
    simpa [prefixWord, tailWord_1317781, baseEnd_1317781] using wordTrace_append hprefix tailTrace_1317781
  have hstable : (prefixWord ++ tailWord_1317781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317781).length < 2 ^ (prefixWord ++ tailWord_1317781).sum := by decide
  have hdescent : baseEnd_1317781 < baseStart_1317781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317841 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 2, 3]
def baseStart_1317841 : Nat := 118140960795 + 1317841 * 2 ^ 59
def prefixEnd_1317841 : Nat := 4983230072969 + 3 ^ 40 * 1317841 * 2
def baseEnd_1317841 : Nat := 451123906134589116484577

theorem tailTrace_1317841 : CollatzResearch.WordTrace tailWord_1317841 prefixEnd_1317841 451123906134589116484577 := by
  unfold tailWord_1317841
  simp only [CollatzResearch.WordTrace]
  refine ⟨48065610018694601169225377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32043740012463067446150251 48065610018694601169225377)
  ·
    refine ⟨36049207514020950876919033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48065610018694601169225377 36049207514020950876919033)
    ·
      refine ⟨27036905635515713157689275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36049207514020950876919033 27036905635515713157689275)
      ·
        refine ⟨40555358453273569736533913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27036905635515713157689275 40555358453273569736533913)
        ·
          refine ⟨30416518839955177302400435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40555358453273569736533913 30416518839955177302400435)
          ·
            refine ⟨45624778259932765953600653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30416518839955177302400435 45624778259932765953600653)
            ·
              refine ⟨17109291847474787232600245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45624778259932765953600653 17109291847474787232600245)
              ·
                refine ⟨1603996110700761303056273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17109291847474787232600245 1603996110700761303056273)
                ·
                  refine ⟨1202997083025570977292205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1603996110700761303056273 1202997083025570977292205)
                  ·
                    refine ⟨451123906134589116484577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202997083025570977292205 451123906134589116484577)
                    ·
                      rfl

theorem cell22_1317841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_1317841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317841 prefixEnd_1317841 := by exact prefixLift 1317841
  have htrace : WordTrace (prefixWord ++ tailWord_1317841) baseStart_1317841 baseEnd_1317841 := by
    simpa [prefixWord, tailWord_1317841, baseEnd_1317841] using wordTrace_append hprefix tailTrace_1317841
  have hstable : (prefixWord ++ tailWord_1317841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317841).length < 2 ^ (prefixWord ++ tailWord_1317841).sum := by decide
  have hdescent : baseEnd_1317841 < baseStart_1317841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317858 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1317858 : Nat := 118140960795 + 1317858 * 2 ^ 59
def prefixEnd_1317858 : Nat := 4983230072969 + 3 ^ 40 * 1317858 * 2
def baseEnd_1317858 : Nat := 451129725582006738809525

theorem tailTrace_1317858 : CollatzResearch.WordTrace tailWord_1317858 prefixEnd_1317858 451129725582006738809525 := by
  unfold tailWord_1317858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12016557514908253268148557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32044153373088675381729485 12016557514908253268148557)
  ·
    refine ⟨4506209068090594975555709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12016557514908253268148557 4506209068090594975555709)
    ·
      refine ⟨1689828400533973115833391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4506209068090594975555709 1689828400533973115833391)
      ·
        refine ⟨2534742600800959673750087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689828400533973115833391 2534742600800959673750087)
        ·
          refine ⟨3802113901201439510625131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534742600800959673750087 3802113901201439510625131)
          ·
            refine ⟨5703170851802159265937697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802113901201439510625131 5703170851802159265937697)
            ·
              refine ⟨4277378138851619449453273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5703170851802159265937697 4277378138851619449453273)
              ·
                refine ⟨3208033604138714587089955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4277378138851619449453273 3208033604138714587089955)
                ·
                  refine ⟨4812050406208071880634933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208033604138714587089955 4812050406208071880634933)
                  ·
                    refine ⟨451129725582006738809525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4812050406208071880634933 451129725582006738809525)
                    ·
                      rfl

theorem cell22_1317858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1317858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317858 prefixEnd_1317858 := by exact prefixLift 1317858
  have htrace : WordTrace (prefixWord ++ tailWord_1317858) baseStart_1317858 baseEnd_1317858 := by
    simpa [prefixWord, tailWord_1317858, baseEnd_1317858] using wordTrace_append hprefix tailTrace_1317858
  have hstable : (prefixWord ++ tailWord_1317858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317858).length < 2 ^ (prefixWord ++ tailWord_1317858).sum := by decide
  have hdescent : baseEnd_1317858 < baseStart_1317858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317950 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1317950 : Nat := 118140960795 + 1317950 * 2 ^ 59
def prefixEnd_1317950 : Nat := 4983230072969 + 3 ^ 40 * 1317950 * 2
def baseEnd_1317950 : Nat := 150387073020716388503081

theorem tailTrace_1317950 : CollatzResearch.WordTrace tailWord_1317950 prefixEnd_1317950 150387073020716388503081 := by
  unfold tailWord_1317950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6008698196912464098117913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32046390383533141856628869 6008698196912464098117913)
  ·
    refine ⟨4506523647684348073588435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6008698196912464098117913 4506523647684348073588435)
    ·
      refine ⟨6759785471526522110382653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4506523647684348073588435 6759785471526522110382653)
      ·
        refine ⟨2534919551822445791393495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6759785471526522110382653 2534919551822445791393495)
        ·
          refine ⟨3802379327733668687090243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2534919551822445791393495 3802379327733668687090243)
          ·
            refine ⟨5703568991600503030635365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802379327733668687090243 5703568991600503030635365)
            ·
              refine ⟨1069419185925094318244131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5703568991600503030635365 1069419185925094318244131)
              ·
                refine ⟨1604128778887641477366197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069419185925094318244131 1604128778887641477366197)
                ·
                  refine ⟨150387073020716388503081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1604128778887641477366197 150387073020716388503081)
                  ·
                    rfl

theorem cell22_1317950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1317950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317950 prefixEnd_1317950 := by exact prefixLift 1317950
  have htrace : WordTrace (prefixWord ++ tailWord_1317950) baseStart_1317950 baseEnd_1317950 := by
    simpa [prefixWord, tailWord_1317950, baseEnd_1317950] using wordTrace_append hprefix tailTrace_1317950
  have hstable : (prefixWord ++ tailWord_1317950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317950).length < 2 ^ (prefixWord ++ tailWord_1317950).sum := by decide
  have hdescent : baseEnd_1317950 < baseStart_1317950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317976 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_1317976 : Nat := 118140960795 + 1317976 * 2 ^ 59
def prefixEnd_1317976 : Nat := 4983230072969 + 3 ^ 40 * 1317976 * 2
def baseEnd_1317976 : Nat := 451170119393493764359163

theorem tailTrace_1317976 : CollatzResearch.WordTrace tailWord_1317976 prefixEnd_1317976 451170119393493764359163 := by
  unfold tailWord_1317976
  simp only [CollatzResearch.WordTrace]
  refine ⟨24035266936602759612694891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32047022582137012816926521 24035266936602759612694891)
  ·
    refine ⟨36052900404904139419042337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24035266936602759612694891 36052900404904139419042337)
    ·
      refine ⟨27039675303678104564281753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36052900404904139419042337 27039675303678104564281753)
      ·
        refine ⟨20279756477758578423211315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27039675303678104564281753 20279756477758578423211315)
        ·
          refine ⟨30419634716637867634816973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20279756477758578423211315 30419634716637867634816973)
          ·
            refine ⟨11407363018739200363056365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30419634716637867634816973 11407363018739200363056365)
            ·
              refine ⟨4277761132027200136146137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11407363018739200363056365 4277761132027200136146137)
              ·
                refine ⟨3208320849020400102109603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4277761132027200136146137 3208320849020400102109603)
                ·
                  refine ⟨4812481273530600153164405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208320849020400102109603 4812481273530600153164405)
                  ·
                    refine ⟨451170119393493764359163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4812481273530600153164405 451170119393493764359163)
                    ·
                      rfl

theorem cell22_1317976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_1317976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317976 prefixEnd_1317976 := by exact prefixLift 1317976
  have htrace : WordTrace (prefixWord ++ tailWord_1317976) baseStart_1317976 baseEnd_1317976 := by
    simpa [prefixWord, tailWord_1317976, baseEnd_1317976] using wordTrace_append hprefix tailTrace_1317976
  have hstable : (prefixWord ++ tailWord_1317976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317976).length < 2 ^ (prefixWord ++ tailWord_1317976).sum := by decide
  have hdescent : baseEnd_1317976 < baseStart_1317976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317980 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1317980 : Nat := 118140960795 + 1317980 * 2 ^ 59
def prefixEnd_1317980 : Nat := 4983230072969 + 3 ^ 40 * 1317980 * 2
def baseEnd_1317980 : Nat := 451171488675239087259151

theorem tailTrace_1317980 : CollatzResearch.WordTrace tailWord_1317980 prefixEnd_1317980 451171488675239087259151 := by
  unfold tailWord_1317980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24035339882595513954267697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32047119843460685272356929 24035339882595513954267697)
  ·
    refine ⟨18026504911946635465700773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24035339882595513954267697 18026504911946635465700773)
    ·
      refine ⟨3379969670989994149818895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18026504911946635465700773 3379969670989994149818895)
      ·
        refine ⟨5069954506484991224728343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379969670989994149818895 5069954506484991224728343)
        ·
          refine ⟨7604931759727486837092515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5069954506484991224728343 7604931759727486837092515)
          ·
            refine ⟨11407397639591230255638773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7604931759727486837092515 11407397639591230255638773)
            ·
              refine ⟨1069443528711677836466135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11407397639591230255638773 1069443528711677836466135)
              ·
                refine ⟨1604165293067516754699203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069443528711677836466135 1604165293067516754699203)
                ·
                  refine ⟨2406247939601275132048805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604165293067516754699203 2406247939601275132048805)
                  ·
                    refine ⟨451171488675239087259151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2406247939601275132048805 451171488675239087259151)
                    ·
                      rfl

theorem cell22_1317980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1317980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317980 prefixEnd_1317980 := by exact prefixLift 1317980
  have htrace : WordTrace (prefixWord ++ tailWord_1317980) baseStart_1317980 baseEnd_1317980 := by
    simpa [prefixWord, tailWord_1317980, baseEnd_1317980] using wordTrace_append hprefix tailTrace_1317980
  have hstable : (prefixWord ++ tailWord_1317980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317980).length < 2 ^ (prefixWord ++ tailWord_1317980).sum := by decide
  have hdescent : baseEnd_1317980 < baseStart_1317980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317993 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 2, 3]
def baseStart_1317993 : Nat := 118140960795 + 1317993 * 2 ^ 59
def prefixEnd_1317993 : Nat := 4983230072969 + 3 ^ 40 * 1317993 * 2
def baseEnd_1317993 : Nat := 451175938840911386684111

theorem tailTrace_1317993 : CollatzResearch.WordTrace tailWord_1317993 prefixEnd_1317993 451175938840911386684111 := by
  unfold tailWord_1317993
  simp only [CollatzResearch.WordTrace]
  refine ⟨48071153914143931128758633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32047435942762620752505755 48071153914143931128758633)
  ·
    refine ⟨36053365435607948346568975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48071153914143931128758633 36053365435607948346568975)
    ·
      refine ⟨54080048153411922519853463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36053365435607948346568975 54080048153411922519853463)
      ·
        refine ⟨81120072230117883779780195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54080048153411922519853463 81120072230117883779780195)
        ·
          refine ⟨121680108345176825669670293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81120072230117883779780195 121680108345176825669670293)
          ·
            refine ⟨5703755078680163703265795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121680108345176825669670293 5703755078680163703265795)
            ·
              refine ⟨8555632618020245554898693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5703755078680163703265795 8555632618020245554898693)
              ·
                refine ⟨1604181115878796041543505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8555632618020245554898693 1604181115878796041543505)
                ·
                  refine ⟨1203135836909097031157629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1604181115878796041543505 1203135836909097031157629)
                  ·
                    refine ⟨451175938840911386684111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203135836909097031157629 451175938840911386684111)
                    ·
                      rfl

theorem cell22_1317993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_1317993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1317993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1317993 prefixEnd_1317993 := by exact prefixLift 1317993
  have htrace : WordTrace (prefixWord ++ tailWord_1317993) baseStart_1317993 baseEnd_1317993 := by
    simpa [prefixWord, tailWord_1317993, baseEnd_1317993] using wordTrace_append hprefix tailTrace_1317993
  have hstable : (prefixWord ++ tailWord_1317993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317993).length < 2 ^ (prefixWord ++ tailWord_1317993).sum := by decide
  have hdescent : baseEnd_1317993 < baseStart_1317993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318055 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1318055 : Nat := 118140960795 + 1318055 * 2 ^ 59
def prefixEnd_1318055 : Nat := 4983230072969 + 3 ^ 40 * 1318055 * 2
def baseEnd_1318055 : Nat := 451197162707963891633921

theorem tailTrace_1318055 : CollatzResearch.WordTrace tailWord_1318055 prefixEnd_1318055 451197162707963891633921 := by
  unfold tailWord_1318055
  simp only [CollatzResearch.WordTrace]
  refine ⟨48073415239919315717515619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32048943493279543811677079 48073415239919315717515619)
  ·
    refine ⟨72110122859878973576273429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48073415239919315717515619 72110122859878973576273429)
    ·
      refine ⟨3380162009056826886387817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72110122859878973576273429 3380162009056826886387817)
      ·
        refine ⟨2535121506792620164790863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3380162009056826886387817 2535121506792620164790863)
        ·
          refine ⟨3802682260188930247186295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535121506792620164790863 3802682260188930247186295)
          ·
            refine ⟨5704023390283395370779443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802682260188930247186295 5704023390283395370779443)
            ·
              refine ⟨8556035085425093056169165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704023390283395370779443 8556035085425093056169165)
              ·
                refine ⟨3208513157034409896063437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8556035085425093056169165 3208513157034409896063437)
                ·
                  refine ⟨1203192433887903711023789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3208513157034409896063437 1203192433887903711023789)
                  ·
                    refine ⟨451197162707963891633921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203192433887903711023789 451197162707963891633921)
                    ·
                      rfl

theorem cell22_1318055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1318055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318055 prefixEnd_1318055 := by exact prefixLift 1318055
  have htrace : WordTrace (prefixWord ++ tailWord_1318055) baseStart_1318055 baseEnd_1318055 := by
    simpa [prefixWord, tailWord_1318055, baseEnd_1318055] using wordTrace_append hprefix tailTrace_1318055
  have hstable : (prefixWord ++ tailWord_1318055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318055).length < 2 ^ (prefixWord ++ tailWord_1318055).sum := by decide
  have hdescent : baseEnd_1318055 < baseStart_1318055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318113 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 6]
def baseStart_1318113 : Nat := 118140960795 + 1318113 * 2 ^ 59
def prefixEnd_1318113 : Nat := 4983230072969 + 3 ^ 40 * 1318113 * 2
def baseEnd_1318113 : Nat := 150405672431090357894581

theorem tailTrace_1318113 : CollatzResearch.WordTrace tailWord_1318113 prefixEnd_1318113 150405672431090357894581 := by
  unfold tailWord_1318113
  simp only [CollatzResearch.WordTrace]
  refine ⟨48075530673709191623126993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32050353782472794415417995 48075530673709191623126993)
  ·
    refine ⟨36056648005281893717345245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48075530673709191623126993 36056648005281893717345245)
    ·
      refine ⟨13521243001980710144004467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36056648005281893717345245 13521243001980710144004467)
      ·
        refine ⟨20281864502971065216006701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13521243001980710144004467 20281864502971065216006701)
        ·
          refine ⟨7605699188614149456002513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20281864502971065216006701 7605699188614149456002513)
          ·
            refine ⟨5704274391460612092001885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7605699188614149456002513 5704274391460612092001885)
            ·
              refine ⟨2139102896797729534500707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5704274391460612092001885 2139102896797729534500707)
              ·
                refine ⟨3208654345196594301751061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139102896797729534500707 3208654345196594301751061)
                ·
                  refine ⟨150405672431090357894581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3208654345196594301751061 150405672431090357894581)
                  ·
                    rfl

theorem cell22_1318113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_1318113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318113 prefixEnd_1318113 := by exact prefixLift 1318113
  have htrace : WordTrace (prefixWord ++ tailWord_1318113) baseStart_1318113 baseEnd_1318113 := by
    simpa [prefixWord, tailWord_1318113, baseEnd_1318113] using wordTrace_append hprefix tailTrace_1318113
  have hstable : (prefixWord ++ tailWord_1318113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318113).length < 2 ^ (prefixWord ++ tailWord_1318113).sum := by decide
  have hdescent : baseEnd_1318113 < baseStart_1318113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318119 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 5]
def baseStart_1318119 : Nat := 118140960795 + 1318119 * 2 ^ 59
def prefixEnd_1318119 : Nat := 4983230072969 + 3 ^ 40 * 1318119 * 2
def baseEnd_1318119 : Nat := 150406357071963019344575

theorem tailTrace_1318119 : CollatzResearch.WordTrace tailWord_1318119 prefixEnd_1318119 150406357071963019344575 := by
  unfold tailWord_1318119
  simp only [CollatzResearch.WordTrace]
  refine ⟨48075749511687454647845411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32050499674458303098563607 48075749511687454647845411)
  ·
    refine ⟨72113624267531181971768117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48075749511687454647845411 72113624267531181971768117)
    ·
      refine ⟨6760652275081048309853261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72113624267531181971768117 6760652275081048309853261)
      ·
        refine ⟨2535244603155393116194973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6760652275081048309853261 2535244603155393116194973)
        ·
          refine ⟨950716726183272418573115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2535244603155393116194973 950716726183272418573115)
          ·
            refine ⟨1426075089274908627859673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950716726183272418573115 1426075089274908627859673)
            ·
              refine ⟨1069556316956181470894755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426075089274908627859673 1069556316956181470894755)
              ·
                refine ⟨1604334475434272206342133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069556316956181470894755 1604334475434272206342133)
                ·
                  refine ⟨150406357071963019344575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1604334475434272206342133 150406357071963019344575)
                  ·
                    rfl

theorem cell22_1318119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 5].length) (baseStart_1318119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318119 prefixEnd_1318119 := by exact prefixLift 1318119
  have htrace : WordTrace (prefixWord ++ tailWord_1318119) baseStart_1318119 baseEnd_1318119 := by
    simpa [prefixWord, tailWord_1318119, baseEnd_1318119] using wordTrace_append hprefix tailTrace_1318119
  have hstable : (prefixWord ++ tailWord_1318119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318119).length < 2 ^ (prefixWord ++ tailWord_1318119).sum := by decide
  have hdescent : baseEnd_1318119 < baseStart_1318119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318143 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 2, 4]
def baseStart_1318143 : Nat := 118140960795 + 1318143 * 2 ^ 59
def prefixEnd_1318143 : Nat := 4983230072969 + 3 ^ 40 * 1318143 * 2
def baseEnd_1318143 : Nat := 451227286906360995433651

theorem tailTrace_1318143 : CollatzResearch.WordTrace tailWord_1318143 prefixEnd_1318143 451227286906360995433651 := by
  unfold tailWord_1318143
  simp only [CollatzResearch.WordTrace]
  refine ⟨48076624863600506746719083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32051083242400337831146055 48076624863600506746719083)
  ·
    refine ⟨72114937295400760120078625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48076624863600506746719083 72114937295400760120078625)
    ·
      refine ⟨54086202971550570090058969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72114937295400760120078625 54086202971550570090058969)
      ·
        refine ⟨40564652228662927567544227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54086202971550570090058969 40564652228662927567544227)
        ·
          refine ⟨60846978342994391351316341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40564652228662927567544227 60846978342994391351316341)
          ·
            refine ⟨5704404219655724189185907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60846978342994391351316341 5704404219655724189185907)
            ·
              refine ⟨8556606329483586283778861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704404219655724189185907 8556606329483586283778861)
              ·
                refine ⟨3208727373556344856417073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8556606329483586283778861 3208727373556344856417073)
                ·
                  refine ⟨2406545530167258642312805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3208727373556344856417073 2406545530167258642312805)
                  ·
                    refine ⟨451227286906360995433651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2406545530167258642312805 451227286906360995433651)
                    ·
                      rfl

theorem cell22_1318143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_1318143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318143 prefixEnd_1318143 := by exact prefixLift 1318143
  have htrace : WordTrace (prefixWord ++ tailWord_1318143) baseStart_1318143 baseEnd_1318143 := by
    simpa [prefixWord, tailWord_1318143, baseEnd_1318143] using wordTrace_append hprefix tailTrace_1318143
  have hstable : (prefixWord ++ tailWord_1318143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318143).length < 2 ^ (prefixWord ++ tailWord_1318143).sum := by decide
  have hdescent : baseEnd_1318143 < baseStart_1318143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318175 : List Nat := [1, 1, 2, 4, 4, 2, 1, 7]
def baseStart_1318175 : Nat := 118140960795 + 1318175 * 2 ^ 59
def prefixEnd_1318175 : Nat := 4983230072969 + 3 ^ 40 * 1318175 * 2
def baseEnd_1318175 : Nat := 50137582351147064292617

theorem tailTrace_1318175 : CollatzResearch.WordTrace tailWord_1318175 prefixEnd_1318175 50137582351147064292617 := by
  unfold tailWord_1318175
  simp only [CollatzResearch.WordTrace]
  refine ⟨48077791999484576211883979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32051861332989717474589319 48077791999484576211883979)
  ·
    refine ⟨72116687999226864317825969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48077791999484576211883979 72116687999226864317825969)
    ·
      refine ⟨54087515999420148238369477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72116687999226864317825969 54087515999420148238369477)
      ·
        refine ⟨10141409249891277794694277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54087515999420148238369477 10141409249891277794694277)
        ·
          refine ⟨1901514234354614586505177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10141409249891277794694277 1901514234354614586505177)
          ·
            refine ⟨1426135675765960939878883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1901514234354614586505177 1426135675765960939878883)
            ·
              refine ⟨2139203513648941409818325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426135675765960939878883 2139203513648941409818325)
              ·
                refine ⟨50137582351147064292617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2139203513648941409818325 50137582351147064292617)
                ·
                  rfl

theorem cell22_1318175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 7].length) (baseStart_1318175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318175 prefixEnd_1318175 := by exact prefixLift 1318175
  have htrace : WordTrace (prefixWord ++ tailWord_1318175) baseStart_1318175 baseEnd_1318175 := by
    simpa [prefixWord, tailWord_1318175, baseEnd_1318175] using wordTrace_append hprefix tailTrace_1318175
  have hstable : (prefixWord ++ tailWord_1318175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318175).length < 2 ^ (prefixWord ++ tailWord_1318175).sum := by decide
  have hdescent : baseEnd_1318175 < baseStart_1318175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318207 : List Nat := [1, 1, 2, 2, 4, 2, 1, 5, 1, 3]
def baseStart_1318207 : Nat := 118140960795 + 1318207 * 2 ^ 59
def prefixEnd_1318207 : Nat := 4983230072969 + 3 ^ 40 * 1318207 * 2
def baseEnd_1318207 : Nat := 451249195414286161833455

theorem tailTrace_1318207 : CollatzResearch.WordTrace tailWord_1318207 prefixEnd_1318207 451249195414286161833455 := by
  unfold tailWord_1318207
  simp only [CollatzResearch.WordTrace]
  refine ⟨48078959135368645677048875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32052639423579097118032583 48078959135368645677048875)
  ·
    refine ⟨72118438703052968515573313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48078959135368645677048875 72118438703052968515573313)
    ·
      refine ⟨54088829027289726386679985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72118438703052968515573313 54088829027289726386679985)
      ·
        refine ⟨40566621770467294790009989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54088829027289726386679985 40566621770467294790009989)
        ·
          refine ⟨7606241581962617773126873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40566621770467294790009989 7606241581962617773126873)
          ·
            refine ⟨5704681186471963329845155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7606241581962617773126873 5704681186471963329845155)
            ·
              refine ⟨8557021779707944994767733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704681186471963329845155 8557021779707944994767733)
              ·
                refine ⟨802220791847619843259475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8557021779707944994767733 802220791847619843259475)
                ·
                  refine ⟨1203331187771429764889213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802220791847619843259475 1203331187771429764889213)
                  ·
                    refine ⟨451249195414286161833455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203331187771429764889213 451249195414286161833455)
                    ·
                      rfl

theorem cell22_1318207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 1, 3].length) (baseStart_1318207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318207 prefixEnd_1318207 := by exact prefixLift 1318207
  have htrace : WordTrace (prefixWord ++ tailWord_1318207) baseStart_1318207 baseEnd_1318207 := by
    simpa [prefixWord, tailWord_1318207, baseEnd_1318207] using wordTrace_append hprefix tailTrace_1318207
  have hstable : (prefixWord ++ tailWord_1318207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318207).length < 2 ^ (prefixWord ++ tailWord_1318207).sum := by decide
  have hdescent : baseEnd_1318207 < baseStart_1318207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318220 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 5]
def baseStart_1318220 : Nat := 118140960795 + 1318220 * 2 ^ 59
def prefixEnd_1318220 : Nat := 4983230072969 + 3 ^ 40 * 1318220 * 2
def baseEnd_1318220 : Nat := 150417881859986153752805

theorem tailTrace_1318220 : CollatzResearch.WordTrace tailWord_1318220 prefixEnd_1318220 150417881859986153752805 := by
  unfold tailWord_1318220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24039716642160774448636057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32052955522881032598181409 24039716642160774448636057)
  ·
    refine ⟨18029787481620580836477043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24039716642160774448636057 18029787481620580836477043)
    ·
      refine ⟨27044681222430871254715565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18029787481620580836477043 27044681222430871254715565)
      ·
        refine ⟨10141755458411576720518337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27044681222430871254715565 10141755458411576720518337)
        ·
          refine ⟨7606316593808682540388753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10141755458411576720518337 7606316593808682540388753)
          ·
            refine ⟨5704737445356511905291565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7606316593808682540388753 5704737445356511905291565)
            ·
              refine ⟨2139276542008691964484337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5704737445356511905291565 2139276542008691964484337)
              ·
                refine ⟨1604457406506518973363253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139276542008691964484337 1604457406506518973363253)
                ·
                  refine ⟨150417881859986153752805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1604457406506518973363253 150417881859986153752805)
                  ·
                    rfl

theorem cell22_1318220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_1318220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318220 prefixEnd_1318220 := by exact prefixLift 1318220
  have htrace : WordTrace (prefixWord ++ tailWord_1318220) baseStart_1318220 baseEnd_1318220 := by
    simpa [prefixWord, tailWord_1318220, baseEnd_1318220] using wordTrace_append hprefix tailTrace_1318220
  have hstable : (prefixWord ++ tailWord_1318220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318220).length < 2 ^ (prefixWord ++ tailWord_1318220).sum := by decide
  have hdescent : baseEnd_1318220 < baseStart_1318220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318230 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1318230 : Nat := 118140960795 + 1318230 * 2 ^ 59
def prefixEnd_1318230 : Nat := 4983230072969 + 3 ^ 40 * 1318230 * 2
def baseEnd_1318230 : Nat := 451257068784321768508385

theorem tailTrace_1318230 : CollatzResearch.WordTrace tailWord_1318230 prefixEnd_1318230 451257068784321768508385 := by
  unfold tailWord_1318230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004987375892832537821009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32053198676190213736757429 3004987375892832537821009)
  ·
    refine ⟨2253740531919624403365757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3004987375892832537821009 2253740531919624403365757)
    ·
      refine ⟨845152699469859151262159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2253740531919624403365757 845152699469859151262159)
      ·
        refine ⟨1267729049204788726893239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845152699469859151262159 1267729049204788726893239)
        ·
          refine ⟨1901593573807183090339859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267729049204788726893239 1901593573807183090339859)
          ·
            refine ⟨2852390360710774635509789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901593573807183090339859 2852390360710774635509789)
            ·
              refine ⟨1069646385266540488316171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2852390360710774635509789 1069646385266540488316171)
              ·
                refine ⟨1604469577899810732474257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069646385266540488316171 1604469577899810732474257)
                ·
                  refine ⟨1203352183424858049355693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1604469577899810732474257 1203352183424858049355693)
                  ·
                    refine ⟨451257068784321768508385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203352183424858049355693 451257068784321768508385)
                    ·
                      rfl

theorem cell22_1318230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1318230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318230 prefixEnd_1318230 := by exact prefixLift 1318230
  have htrace : WordTrace (prefixWord ++ tailWord_1318230) baseStart_1318230 baseEnd_1318230 := by
    simpa [prefixWord, tailWord_1318230, baseEnd_1318230] using wordTrace_append hprefix tailTrace_1318230
  have hstable : (prefixWord ++ tailWord_1318230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318230).length < 2 ^ (prefixWord ++ tailWord_1318230).sum := by decide
  have hdescent : baseEnd_1318230 < baseStart_1318230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318233 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_1318233 : Nat := 118140960795 + 1318233 * 2 ^ 59
def prefixEnd_1318233 : Nat := 4983230072969 + 3 ^ 40 * 1318233 * 2
def baseEnd_1318233 : Nat := 451258095745630760683375

theorem tailTrace_1318233 : CollatzResearch.WordTrace tailWord_1318233 prefixEnd_1318233 451258095745630760683375 := by
  unfold tailWord_1318233
  simp only [CollatzResearch.WordTrace]
  refine ⟨48079907433274452117495353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32053271622182968078330235 48079907433274452117495353)
  ·
    refine ⟨36059930574955839088121515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48079907433274452117495353 36059930574955839088121515)
    ·
      refine ⟨54089895862433758632182273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36059930574955839088121515 54089895862433758632182273)
      ·
        refine ⟨40567421896825318974136705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54089895862433758632182273 40567421896825318974136705)
        ·
          refine ⟨30425566422618989230602529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40567421896825318974136705 30425566422618989230602529)
          ·
            refine ⟨22819174816964241922951897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30425566422618989230602529 22819174816964241922951897)
            ·
              refine ⟨17114381112723181442213923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22819174816964241922951897 17114381112723181442213923)
              ·
                refine ⟨25671571669084772163320885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17114381112723181442213923 25671571669084772163320885)
                ·
                  refine ⟨2406709843976697390311333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25671571669084772163320885 2406709843976697390311333)
                  ·
                    refine ⟨451258095745630760683375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2406709843976697390311333 451258095745630760683375)
                    ·
                      rfl

theorem cell22_1318233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_1318233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318233 prefixEnd_1318233 := by exact prefixLift 1318233
  have htrace : WordTrace (prefixWord ++ tailWord_1318233) baseStart_1318233 baseEnd_1318233 := by
    simpa [prefixWord, tailWord_1318233, baseEnd_1318233] using wordTrace_append hprefix tailTrace_1318233
  have hstable : (prefixWord ++ tailWord_1318233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318233).length < 2 ^ (prefixWord ++ tailWord_1318233).sum := by decide
  have hdescent : baseEnd_1318233 < baseStart_1318233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318263 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 3, 5]
def baseStart_1318263 : Nat := 118140960795 + 1318263 * 2 ^ 59
def prefixEnd_1318263 : Nat := 4983230072969 + 3 ^ 40 * 1318263 * 2
def baseEnd_1318263 : Nat := 451268365358720682433283

theorem tailTrace_1318263 : CollatzResearch.WordTrace tailWord_1318263 prefixEnd_1318263 451268365358720682433283 := by
  unfold tailWord_1318263
  simp only [CollatzResearch.WordTrace]
  refine ⟨48081001623165767241087443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32054001082110511494058295 48081001623165767241087443)
  ·
    refine ⟨72121502434748650861631165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48081001623165767241087443 72121502434748650861631165)
    ·
      refine ⟨27045563413030744073111687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72121502434748650861631165 27045563413030744073111687)
      ·
        refine ⟨40568345119546116109667531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27045563413030744073111687 40568345119546116109667531)
        ·
          refine ⟨60852517679319174164501297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40568345119546116109667531 60852517679319174164501297)
          ·
            refine ⟨45639388259489380623375973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60852517679319174164501297 45639388259489380623375973)
            ·
              refine ⟨8557385298654258866882995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45639388259489380623375973 8557385298654258866882995)
              ·
                refine ⟨12836077947981388300324493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557385298654258866882995 12836077947981388300324493)
                ·
                  refine ⟨4813529230493020612621685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12836077947981388300324493 4813529230493020612621685)
                  ·
                    refine ⟨451268365358720682433283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4813529230493020612621685 451268365358720682433283)
                    ·
                      rfl

theorem cell22_1318263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_1318263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318263 prefixEnd_1318263 := by exact prefixLift 1318263
  have htrace : WordTrace (prefixWord ++ tailWord_1318263) baseStart_1318263 baseEnd_1318263 := by
    simpa [prefixWord, tailWord_1318263, baseEnd_1318263] using wordTrace_append hprefix tailTrace_1318263
  have hstable : (prefixWord ++ tailWord_1318263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318263).length < 2 ^ (prefixWord ++ tailWord_1318263).sum := by decide
  have hdescent : baseEnd_1318263 < baseStart_1318263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318293 : List Nat := [1, 3, 2, 1, 1, 2, 3, 9]
def baseStart_1318293 : Nat := 118140960795 + 1318293 * 2 ^ 59
def prefixEnd_1318293 : Nat := 4983230072969 + 3 ^ 40 * 1318293 * 2
def baseEnd_1318293 : Nat := 50142070552423400464799

theorem tailTrace_1318293 : CollatzResearch.WordTrace tailWord_1318293 prefixEnd_1318293 50142070552423400464799 := by
  unfold tailWord_1318293
  simp only [CollatzResearch.WordTrace]
  refine ⟨48082095813057082364679533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32054730542038054909786355 48082095813057082364679533)
  ·
    refine ⟨18030785929896405886754825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48082095813057082364679533 18030785929896405886754825)
    ·
      refine ⟨13523089447422304415066119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18030785929896405886754825 13523089447422304415066119)
      ·
        refine ⟨20284634171133456622599179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13523089447422304415066119 20284634171133456622599179)
        ·
          refine ⟨30426951256700184933898769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20284634171133456622599179 30426951256700184933898769)
          ·
            refine ⟨22820213442525138700424077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30426951256700184933898769 22820213442525138700424077)
            ·
              refine ⟨8557580040946927012659029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22820213442525138700424077 8557580040946927012659029)
              ·
                refine ⟨50142070552423400464799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8557580040946927012659029 50142070552423400464799)
                ·
                  rfl

theorem cell22_1318293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 9].length) (baseStart_1318293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318293 prefixEnd_1318293 := by exact prefixLift 1318293
  have htrace : WordTrace (prefixWord ++ tailWord_1318293) baseStart_1318293 baseEnd_1318293 := by
    simpa [prefixWord, tailWord_1318293, baseEnd_1318293] using wordTrace_append hprefix tailTrace_1318293
  have hstable : (prefixWord ++ tailWord_1318293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318293).length < 2 ^ (prefixWord ++ tailWord_1318293).sum := by decide
  have hdescent : baseEnd_1318293 < baseStart_1318293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318297 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 2, 3]
def baseStart_1318297 : Nat := 118140960795 + 1318297 * 2 ^ 59
def prefixEnd_1318297 : Nat := 4983230072969 + 3 ^ 40 * 1318297 * 2
def baseEnd_1318297 : Nat := 451280004253555927083179

theorem tailTrace_1318297 : CollatzResearch.WordTrace tailWord_1318297 prefixEnd_1318297 451280004253555927083179 := by
  unfold tailWord_1318297
  simp only [CollatzResearch.WordTrace]
  refine ⟨48082241705042591047825145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32054827803361727365216763 48082241705042591047825145)
  ·
    refine ⟨36061681278781943285868859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48082241705042591047825145 36061681278781943285868859)
    ·
      refine ⟨54092521918172914928803289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36061681278781943285868859 54092521918172914928803289)
      ·
        refine ⟨40569391438629686196602467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54092521918172914928803289 40569391438629686196602467)
        ·
          refine ⟨60854087157944529294903701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40569391438629686196602467 60854087157944529294903701)
          ·
            refine ⟨2852535335528649810698611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60854087157944529294903701 2852535335528649810698611)
            ·
              refine ⟨4278803003292974716047917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852535335528649810698611 4278803003292974716047917)
              ·
                refine ⟨1604551126234865518517969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4278803003292974716047917 1604551126234865518517969)
                ·
                  refine ⟨1203413344676149138888477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1604551126234865518517969 1203413344676149138888477)
                  ·
                    refine ⟨451280004253555927083179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203413344676149138888477 451280004253555927083179)
                    ·
                      rfl

theorem cell22_1318297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_1318297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318297 prefixEnd_1318297 := by exact prefixLift 1318297
  have htrace : WordTrace (prefixWord ++ tailWord_1318297) baseStart_1318297 baseEnd_1318297 := by
    simpa [prefixWord, tailWord_1318297, baseEnd_1318297] using wordTrace_append hprefix tailTrace_1318297
  have hstable : (prefixWord ++ tailWord_1318297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318297).length < 2 ^ (prefixWord ++ tailWord_1318297).sum := by decide
  have hdescent : baseEnd_1318297 < baseStart_1318297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318323 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 4, 6]
def baseStart_1318323 : Nat := 118140960795 + 1318323 * 2 ^ 59
def prefixEnd_1318323 : Nat := 4983230072969 + 3 ^ 40 * 1318323 * 2
def baseEnd_1318323 : Nat := 451288904584900525933099

theorem tailTrace_1318323 : CollatzResearch.WordTrace tailWord_1318323 prefixEnd_1318323 451288904584900525933099 := by
  unfold tailWord_1318323
  simp only [CollatzResearch.WordTrace]
  refine ⟨48083190002948397488271623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32055460001965598325514415 48083190002948397488271623)
  ·
    refine ⟨72124785004422596232407435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48083190002948397488271623 72124785004422596232407435)
    ·
      refine ⟨108187177506633894348611153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72124785004422596232407435 108187177506633894348611153)
      ·
        refine ⟨81140383129975420761458365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108187177506633894348611153 81140383129975420761458365)
        ·
          refine ⟨30427643673740782785546887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81140383129975420761458365 30427643673740782785546887)
          ·
            refine ⟨45641465510611174178320331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30427643673740782785546887 45641465510611174178320331)
            ·
              refine ⟨68462198265916761267480497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45641465510611174178320331 68462198265916761267480497)
              ·
                refine ⟨51346648699437570950610373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68462198265916761267480497 51346648699437570950610373)
                ·
                  refine ⟨9627496631144544553239445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51346648699437570950610373 9627496631144544553239445)
                  ·
                    refine ⟨451288904584900525933099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9627496631144544553239445 451288904584900525933099)
                    ·
                      rfl

theorem cell22_1318323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_1318323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318323 prefixEnd_1318323 := by exact prefixLift 1318323
  have htrace : WordTrace (prefixWord ++ tailWord_1318323) baseStart_1318323 baseEnd_1318323 := by
    simpa [prefixWord, tailWord_1318323, baseEnd_1318323] using wordTrace_append hprefix tailTrace_1318323
  have hstable : (prefixWord ++ tailWord_1318323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318323).length < 2 ^ (prefixWord ++ tailWord_1318323).sum := by decide
  have hdescent : baseEnd_1318323 < baseStart_1318323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318389 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 5]
def baseStart_1318389 : Nat := 118140960795 + 1318389 * 2 ^ 59
def prefixEnd_1318389 : Nat := 4983230072969 + 3 ^ 40 * 1318389 * 2
def baseEnd_1318389 : Nat := 150437165911232784594299

theorem tailTrace_1318389 : CollatzResearch.WordTrace tailWord_1318389 prefixEnd_1318389 150437165911232784594299 := by
  unfold tailWord_1318389
  simp only [CollatzResearch.WordTrace]
  refine ⟨48085597220709290760174221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32057064813806193840116147 48085597220709290760174221)
  ·
    refine ⟨18032098957765984035065333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48085597220709290760174221 18032098957765984035065333)
    ·
      refine ⟨1690509277290561003287375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18032098957765984035065333 1690509277290561003287375)
      ·
        refine ⟨2535763915935841504931063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1690509277290561003287375 2535763915935841504931063)
        ·
          refine ⟨3803645873903762257396595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535763915935841504931063 3803645873903762257396595)
          ·
            refine ⟨5705468810855643386094893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3803645873903762257396595 5705468810855643386094893)
            ·
              refine ⟨2139550804070866269785585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5705468810855643386094893 2139550804070866269785585)
              ·
                refine ⟨1604663103053149702339189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139550804070866269785585 1604663103053149702339189)
                ·
                  refine ⟨150437165911232784594299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1604663103053149702339189 150437165911232784594299)
                  ·
                    rfl

theorem cell22_1318389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_1318389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318389 prefixEnd_1318389 := by exact prefixLift 1318389
  have htrace : WordTrace (prefixWord ++ tailWord_1318389) baseStart_1318389 baseEnd_1318389 := by
    simpa [prefixWord, tailWord_1318389, baseEnd_1318389] using wordTrace_append hprefix tailTrace_1318389
  have hstable : (prefixWord ++ tailWord_1318389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318389).length < 2 ^ (prefixWord ++ tailWord_1318389).sum := by decide
  have hdescent : baseEnd_1318389 < baseStart_1318389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318434 : List Nat := [3, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1318434 : Nat := 118140960795 + 1318434 * 2 ^ 59
def prefixEnd_1318434 : Nat := 4983230072969 + 3 ^ 40 * 1318434 * 2
def baseEnd_1318434 : Nat := 150442300717777745469253

theorem tailTrace_1318434 : CollatzResearch.WordTrace tailWord_1318434 prefixEnd_1318434 150442300717777745469253 := by
  unfold tailWord_1318434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021809626386565861390589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32058159003697508963708237 12021809626386565861390589)
  ·
    refine ⟨4508178609894962198021471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12021809626386565861390589 4508178609894962198021471)
    ·
      refine ⟨6762267914842443297032207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508178609894962198021471 6762267914842443297032207)
      ·
        refine ⟨10143401872263664945548311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6762267914842443297032207 10143401872263664945548311)
        ·
          refine ⟨15215102808395497418322467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10143401872263664945548311 15215102808395497418322467)
          ·
            refine ⟨22822654212593246127483701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15215102808395497418322467 22822654212593246127483701)
            ·
              refine ⟨2139623832430616824451597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22822654212593246127483701 2139623832430616824451597)
              ·
                refine ⟨802358937161481309169349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2139623832430616824451597 802358937161481309169349)
                ·
                  refine ⟨150442300717777745469253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802358937161481309169349 150442300717777745469253)
                  ·
                    rfl

theorem cell22_1318434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1318434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318434 prefixEnd_1318434 := by exact prefixLift 1318434
  have htrace : WordTrace (prefixWord ++ tailWord_1318434) baseStart_1318434 baseEnd_1318434 := by
    simpa [prefixWord, tailWord_1318434, baseEnd_1318434] using wordTrace_append hprefix tailTrace_1318434
  have hstable : (prefixWord ++ tailWord_1318434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318434).length < 2 ^ (prefixWord ++ tailWord_1318434).sum := by decide
  have hdescent : baseEnd_1318434 < baseStart_1318434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318470 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1318470 : Nat := 118140960795 + 1318470 * 2 ^ 59
def prefixEnd_1318470 : Nat := 4983230072969 + 3 ^ 40 * 1318470 * 2
def baseEnd_1318470 : Nat := 451339225689041142507649

theorem tailTrace_1318470 : CollatzResearch.WordTrace tailWord_1318470 prefixEnd_1318470 451339225689041142507649 := by
  unfold tailWord_1318470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502767235419245049808527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32059034355610561062581909 1502767235419245049808527)
  ·
    refine ⟨2254150853128867574712791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1502767235419245049808527 2254150853128867574712791)
    ·
      refine ⟨3381226279693301362069187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2254150853128867574712791 3381226279693301362069187)
      ·
        refine ⟨5071839419539952043103781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381226279693301362069187 5071839419539952043103781)
        ·
          refine ⟨950969891163741008081959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5071839419539952043103781 950969891163741008081959)
          ·
            refine ⟨1426454836745611512122939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950969891163741008081959 1426454836745611512122939)
            ·
              refine ⟨2139682255118417268184409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426454836745611512122939 2139682255118417268184409)
              ·
                refine ⟨1604761691338812951138307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139682255118417268184409 1604761691338812951138307)
                ·
                  refine ⟨2407142537008219426707461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604761691338812951138307 2407142537008219426707461)
                  ·
                    refine ⟨451339225689041142507649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2407142537008219426707461 451339225689041142507649)
                    ·
                      rfl

theorem cell22_1318470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1318470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318470 prefixEnd_1318470 := by exact prefixLift 1318470
  have htrace : WordTrace (prefixWord ++ tailWord_1318470) baseStart_1318470 baseEnd_1318470 := by
    simpa [prefixWord, tailWord_1318470, baseEnd_1318470] using wordTrace_append hprefix tailTrace_1318470
  have hstable : (prefixWord ++ tailWord_1318470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318470).length < 2 ^ (prefixWord ++ tailWord_1318470).sum := by decide
  have hdescent : baseEnd_1318470 < baseStart_1318470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318490 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_1318490 : Nat := 118140960795 + 1318490 * 2 ^ 59
def prefixEnd_1318490 : Nat := 4983230072969 + 3 ^ 40 * 1318490 * 2
def baseEnd_1318490 : Nat := 150448690699255919002529

theorem tailTrace_1318490 : CollatzResearch.WordTrace tailWord_1318490 prefixEnd_1318490 150448690699255919002529 := by
  unfold tailWord_1318490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12022320248335846252400231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32059520662228923339733949 12022320248335846252400231)
  ·
    refine ⟨18033480372503769378600347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12022320248335846252400231 18033480372503769378600347)
    ·
      refine ⟨27050220558755654067900521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18033480372503769378600347 27050220558755654067900521)
      ·
        refine ⟨20287665419066740550925391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27050220558755654067900521 20287665419066740550925391)
        ·
          refine ⟨30431498128600110826388087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20287665419066740550925391 30431498128600110826388087)
          ·
            refine ⟨45647247192900166239582131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30431498128600110826388087 45647247192900166239582131)
            ·
              refine ⟨68470870789350249359373197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45647247192900166239582131 68470870789350249359373197)
              ·
                refine ⟨25676576546006343509764949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68470870789350249359373197 25676576546006343509764949)
                ·
                  refine ⟨150448690699255919002529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25676576546006343509764949 150448690699255919002529)
                  ·
                    rfl

theorem cell22_1318490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_1318490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318490 prefixEnd_1318490 := by exact prefixLift 1318490
  have htrace : WordTrace (prefixWord ++ tailWord_1318490) baseStart_1318490 baseEnd_1318490 := by
    simpa [prefixWord, tailWord_1318490, baseEnd_1318490] using wordTrace_append hprefix tailTrace_1318490
  have hstable : (prefixWord ++ tailWord_1318490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318490).length < 2 ^ (prefixWord ++ tailWord_1318490).sum := by decide
  have hdescent : baseEnd_1318490 < baseStart_1318490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318520 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1318520 : Nat := 118140960795 + 1318520 * 2 ^ 59
def prefixEnd_1318520 : Nat := 4983230072969 + 3 ^ 40 * 1318520 * 2
def baseEnd_1318520 : Nat := 451356341710857678757495

theorem tailTrace_1318520 : CollatzResearch.WordTrace tailWord_1318520 prefixEnd_1318520 451356341710857678757495 := by
  unfold tailWord_1318520
  simp only [CollatzResearch.WordTrace]
  refine ⟨24045187591617350066596507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32060250122156466755462009 24045187591617350066596507)
  ·
    refine ⟨36067781387426025099894761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24045187591617350066596507 36067781387426025099894761)
    ·
      refine ⟨27050836040569518824921071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36067781387426025099894761 27050836040569518824921071)
      ·
        refine ⟨40576254060854278237381607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27050836040569518824921071 40576254060854278237381607)
        ·
          refine ⟨60864381091281417356072411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40576254060854278237381607 60864381091281417356072411)
          ·
            refine ⟨91296571636922126034108617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60864381091281417356072411 91296571636922126034108617)
            ·
              refine ⟨68472428727691594525581463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91296571636922126034108617 68472428727691594525581463)
              ·
                refine ⟨102708643091537391788372195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68472428727691594525581463 102708643091537391788372195)
                ·
                  refine ⟨154062964637306087682558293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102708643091537391788372195 154062964637306087682558293)
                  ·
                    refine ⟨451356341710857678757495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 154062964637306087682558293 451356341710857678757495)
                    ·
                      rfl

theorem cell22_1318520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1318520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318520 prefixEnd_1318520 := by exact prefixLift 1318520
  have htrace : WordTrace (prefixWord ++ tailWord_1318520) baseStart_1318520 baseEnd_1318520 := by
    simpa [prefixWord, tailWord_1318520, baseEnd_1318520] using wordTrace_append hprefix tailTrace_1318520
  have hstable : (prefixWord ++ tailWord_1318520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318520).length < 2 ^ (prefixWord ++ tailWord_1318520).sum := by decide
  have hdescent : baseEnd_1318520 < baseStart_1318520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318537 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_1318537 : Nat := 118140960795 + 1318537 * 2 ^ 59
def prefixEnd_1318537 : Nat := 4983230072969 + 3 ^ 40 * 1318537 * 2
def baseEnd_1318537 : Nat := 451362161158275301082443

theorem tailTrace_1318537 : CollatzResearch.WordTrace tailWord_1318537 prefixEnd_1318537 451362161158275301082443 := by
  unfold tailWord_1318537
  simp only [CollatzResearch.WordTrace]
  refine ⟨48090995224173112036561865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32060663482782074691041243 48090995224173112036561865)
  ·
    refine ⟨36068246418129834027421399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48090995224173112036561865 36068246418129834027421399)
    ·
      refine ⟨54102369627194751041132099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36068246418129834027421399 54102369627194751041132099)
      ·
        refine ⟨81153554440792126561698149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54102369627194751041132099 81153554440792126561698149)
        ·
          refine ⟨15216291457648523730318403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81153554440792126561698149 15216291457648523730318403)
          ·
            refine ⟨22824437186472785595477605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15216291457648523730318403 22824437186472785595477605)
            ·
              refine ⟨4279581972463647299152051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22824437186472785595477605 4279581972463647299152051)
              ·
                refine ⟨6419372958695470948728077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4279581972463647299152051 6419372958695470948728077)
                ·
                  refine ⟨2407264859510801605773029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6419372958695470948728077 2407264859510801605773029)
                  ·
                    refine ⟨451362161158275301082443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2407264859510801605773029 451362161158275301082443)
                    ·
                      rfl

theorem cell22_1318537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_1318537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318537 prefixEnd_1318537 := by exact prefixLift 1318537
  have htrace : WordTrace (prefixWord ++ tailWord_1318537) baseStart_1318537 baseEnd_1318537 := by
    simpa [prefixWord, tailWord_1318537, baseEnd_1318537] using wordTrace_append hprefix tailTrace_1318537
  have hstable : (prefixWord ++ tailWord_1318537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318537).length < 2 ^ (prefixWord ++ tailWord_1318537).sum := by decide
  have hdescent : baseEnd_1318537 < baseStart_1318537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318584 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 2, 3]
def baseStart_1318584 : Nat := 118140960795 + 1318584 * 2 ^ 59
def prefixEnd_1318584 : Nat := 4983230072969 + 3 ^ 40 * 1318584 * 2
def baseEnd_1318584 : Nat := 451378250218782845157299

theorem tailTrace_1318584 : CollatzResearch.WordTrace tailWord_1318584 prefixEnd_1318584 451378250218782845157299 := by
  unfold tailWord_1318584
  simp only [CollatzResearch.WordTrace]
  refine ⟨24046354727501419531761403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32061806303335226042348537 24046354727501419531761403)
  ·
    refine ⟨36069532091252129297642105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24046354727501419531761403 36069532091252129297642105)
    ·
      refine ⟨27052149068439096973231579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36069532091252129297642105 27052149068439096973231579)
      ·
        refine ⟨40578223602658645459847369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27052149068439096973231579 40578223602658645459847369)
        ·
          refine ⟨30433667701993984094885527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40578223602658645459847369 30433667701993984094885527)
          ·
            refine ⟨45650501552990976142328291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30433667701993984094885527 45650501552990976142328291)
            ·
              refine ⟨68475752329486464213492437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45650501552990976142328291 68475752329486464213492437)
              ·
                refine ⟨1604900445222339005003729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68475752329486464213492437 1604900445222339005003729)
                ·
                  refine ⟨1203675333916754253752797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1604900445222339005003729 1203675333916754253752797)
                  ·
                    refine ⟨451378250218782845157299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203675333916754253752797 451378250218782845157299)
                    ·
                      rfl

theorem cell22_1318584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_1318584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318584 prefixEnd_1318584 := by exact prefixLift 1318584
  have htrace : WordTrace (prefixWord ++ tailWord_1318584) baseStart_1318584 baseEnd_1318584 := by
    simpa [prefixWord, tailWord_1318584, baseEnd_1318584] using wordTrace_append hprefix tailTrace_1318584
  have hstable : (prefixWord ++ tailWord_1318584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318584).length < 2 ^ (prefixWord ++ tailWord_1318584).sum := by decide
  have hdescent : baseEnd_1318584 < baseStart_1318584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318620 : List Nat := [2, 2, 5, 1, 2, 1, 3, 2, 4]
def baseStart_1318620 : Nat := 118140960795 + 1318620 * 2 ^ 59
def prefixEnd_1318620 : Nat := 4983230072969 + 3 ^ 40 * 1318620 * 2
def baseEnd_1318620 : Nat := 150463524584830250419063

theorem tailTrace_1318620 : CollatzResearch.WordTrace tailWord_1318620 prefixEnd_1318620 150463524584830250419063 := by
  unfold tailWord_1318620
  simp only [CollatzResearch.WordTrace]
  refine ⟨24047011241436208605916657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32062681655248278141222209 24047011241436208605916657)
  ·
    refine ⟨18035258431077156454437493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24047011241436208605916657 18035258431077156454437493)
    ·
      refine ⟨1690805477913483417603515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18035258431077156454437493 1690805477913483417603515)
      ·
        refine ⟨2536208216870225126405273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1690805477913483417603515 2536208216870225126405273)
        ·
          refine ⟨1902156162652668844803955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2536208216870225126405273 1902156162652668844803955)
          ·
            refine ⟨2853234243979003267205933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902156162652668844803955 2853234243979003267205933)
            ·
              refine ⟨1069962841492126225202225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2853234243979003267205933 1069962841492126225202225)
              ·
                refine ⟨802472131119094668901669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069962841492126225202225 802472131119094668901669)
                ·
                  refine ⟨150463524584830250419063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802472131119094668901669 150463524584830250419063)
                  ·
                    rfl

theorem cell22_1318620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_1318620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318620 prefixEnd_1318620 := by exact prefixLift 1318620
  have htrace : WordTrace (prefixWord ++ tailWord_1318620) baseStart_1318620 baseEnd_1318620 := by
    simpa [prefixWord, tailWord_1318620, baseEnd_1318620] using wordTrace_append hprefix tailTrace_1318620
  have hstable : (prefixWord ++ tailWord_1318620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318620).length < 2 ^ (prefixWord ++ tailWord_1318620).sum := by decide
  have hdescent : baseEnd_1318620 < baseStart_1318620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318631 : List Nat := [1, 1, 5, 4, 1, 1, 2, 7]
def baseStart_1318631 : Nat := 118140960795 + 1318631 * 2 ^ 59
def prefixEnd_1318631 : Nat := 4983230072969 + 3 ^ 40 * 1318631 * 2
def baseEnd_1318631 : Nat := 50154926586587821025795

theorem tailTrace_1318631 : CollatzResearch.WordTrace tailWord_1318631 prefixEnd_1318631 50154926586587821025795 := by
  unfold tailWord_1318631
  simp only [CollatzResearch.WordTrace]
  refine ⟨48094423685832566090483747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32062949123888377393655831 48094423685832566090483747)
  ·
    refine ⟨72141635528748849135725621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48094423685832566090483747 72141635528748849135725621)
    ·
      refine ⟨6763278330820204606474277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72141635528748849135725621 6763278330820204606474277)
      ·
        refine ⟨1268114687028788363713927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6763278330820204606474277 1268114687028788363713927)
        ·
          refine ⟨1902172030543182545570891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268114687028788363713927 1902172030543182545570891)
          ·
            refine ⟨2853258045814773818356337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902172030543182545570891 2853258045814773818356337)
            ·
              refine ⟨2139943534361080363767253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853258045814773818356337 2139943534361080363767253)
              ·
                refine ⟨50154926586587821025795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2139943534361080363767253 50154926586587821025795)
                ·
                  rfl

theorem cell22_1318631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 7].length) (baseStart_1318631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318631 prefixEnd_1318631 := by exact prefixLift 1318631
  have htrace : WordTrace (prefixWord ++ tailWord_1318631) baseStart_1318631 baseEnd_1318631 := by
    simpa [prefixWord, tailWord_1318631, baseEnd_1318631] using wordTrace_append hprefix tailTrace_1318631
  have hstable : (prefixWord ++ tailWord_1318631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318631).length < 2 ^ (prefixWord ++ tailWord_1318631).sum := by decide
  have hdescent : baseEnd_1318631 < baseStart_1318631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318669 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1318669 : Nat := 118140960795 + 1318669 * 2 ^ 59
def prefixEnd_1318669 : Nat := 4983230072969 + 3 ^ 40 * 1318669 * 2
def baseEnd_1318669 : Nat := 451407347455870956782039

theorem tailTrace_1318669 : CollatzResearch.WordTrace tailWord_1318669 prefixEnd_1318669 451407347455870956782039 := by
  unfold tailWord_1318669
  simp only [CollatzResearch.WordTrace]
  refine ⟨48095809659694898580367061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32063873106463265720244707 48095809659694898580367061)
  ·
    refine ⟨1127245538899099185477353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 48095809659694898580367061 1127245538899099185477353)
    ·
      refine ⟨845434154174324389108015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1127245538899099185477353 845434154174324389108015)
      ·
        refine ⟨1268151231261486583662023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845434154174324389108015 1268151231261486583662023)
        ·
          refine ⟨1902226846892229875493035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268151231261486583662023 1902226846892229875493035)
          ·
            refine ⟨2853340270338344813239553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902226846892229875493035 2853340270338344813239553)
            ·
              refine ⟨2140005202753758609929665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853340270338344813239553 2140005202753758609929665)
              ·
                refine ⟨1605003902065318957447249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140005202753758609929665 1605003902065318957447249)
                ·
                  refine ⟨1203752926548989218085437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605003902065318957447249 1203752926548989218085437)
                  ·
                    refine ⟨451407347455870956782039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203752926548989218085437 451407347455870956782039)
                    ·
                      rfl

theorem cell22_1318669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1318669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318669 prefixEnd_1318669 := by exact prefixLift 1318669
  have htrace : WordTrace (prefixWord ++ tailWord_1318669) baseStart_1318669 baseEnd_1318669 := by
    simpa [prefixWord, tailWord_1318669, baseEnd_1318669] using wordTrace_append hprefix tailTrace_1318669
  have hstable : (prefixWord ++ tailWord_1318669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318669).length < 2 ^ (prefixWord ++ tailWord_1318669).sum := by decide
  have hdescent : baseEnd_1318669 < baseStart_1318669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318689 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1318689 : Nat := 118140960795 + 1318689 * 2 ^ 59
def prefixEnd_1318689 : Nat := 4983230072969 + 3 ^ 40 * 1318689 * 2
def baseEnd_1318689 : Nat := 451414193864597571281977

theorem tailTrace_1318689 : CollatzResearch.WordTrace tailWord_1318689 prefixEnd_1318689 451414193864597571281977 := by
  unfold tailWord_1318689
  simp only [CollatzResearch.WordTrace]
  refine ⟨48096539119622441996095121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32064359413081627997396747 48096539119622441996095121)
  ·
    refine ⟨36072404339716831497071341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48096539119622441996095121 36072404339716831497071341)
    ·
      refine ⟨13527151627393811811401753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36072404339716831497071341 13527151627393811811401753)
      ·
        refine ⟨10145363720545358858551315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13527151627393811811401753 10145363720545358858551315)
        ·
          refine ⟨15218045580818038287826973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10145363720545358858551315 15218045580818038287826973)
          ·
            refine ⟨5706767092806764357935115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15218045580818038287826973 5706767092806764357935115)
            ·
              refine ⟨8560150639210146536902673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706767092806764357935115 8560150639210146536902673)
              ·
                refine ⟨6420112979407609902677005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8560150639210146536902673 6420112979407609902677005)
                ·
                  refine ⟨2407542367277853713503877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6420112979407609902677005 2407542367277853713503877)
                  ·
                    refine ⟨451414193864597571281977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2407542367277853713503877 451414193864597571281977)
                    ·
                      rfl

theorem cell22_1318689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1318689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318689 prefixEnd_1318689 := by exact prefixLift 1318689
  have htrace : WordTrace (prefixWord ++ tailWord_1318689) baseStart_1318689 baseEnd_1318689 := by
    simpa [prefixWord, tailWord_1318689, baseEnd_1318689] using wordTrace_append hprefix tailTrace_1318689
  have hstable : (prefixWord ++ tailWord_1318689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318689).length < 2 ^ (prefixWord ++ tailWord_1318689).sum := by decide
  have hdescent : baseEnd_1318689 < baseStart_1318689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318723 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 1, 4]
def baseStart_1318723 : Nat := 118140960795 + 1318723 * 2 ^ 59
def prefixEnd_1318723 : Nat := 4983230072969 + 3 ^ 40 * 1318723 * 2
def baseEnd_1318723 : Nat := 451425832759432815931873

theorem tailTrace_1318723 : CollatzResearch.WordTrace tailWord_1318723 prefixEnd_1318723 451425832759432815931873 := by
  unfold tailWord_1318723
  simp only [CollatzResearch.WordTrace]
  refine ⟨48097779201499265802832823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32065186134332843868555215 48097779201499265802832823)
  ·
    refine ⟨72146668802248898704249235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48097779201499265802832823 72146668802248898704249235)
    ·
      refine ⟨108220003203373348056373853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72146668802248898704249235 108220003203373348056373853)
      ·
        refine ⟨40582501201265005521140195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108220003203373348056373853 40582501201265005521140195)
        ·
          refine ⟨60873751801897508281710293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40582501201265005521140195 60873751801897508281710293)
          ·
            refine ⟨1426728557856972850352585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60873751801897508281710293 1426728557856972850352585)
            ·
              refine ⟨1070046418392729637764439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426728557856972850352585 1070046418392729637764439)
              ·
                refine ⟨1605069627589094456646659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070046418392729637764439 1605069627589094456646659)
                ·
                  refine ⟨2407604441383641684969989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605069627589094456646659 2407604441383641684969989)
                  ·
                    refine ⟨451425832759432815931873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2407604441383641684969989 451425832759432815931873)
                    ·
                      rfl

theorem cell22_1318723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 4].length) (baseStart_1318723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318723 prefixEnd_1318723 := by exact prefixLift 1318723
  have htrace : WordTrace (prefixWord ++ tailWord_1318723) baseStart_1318723 baseEnd_1318723 := by
    simpa [prefixWord, tailWord_1318723, baseEnd_1318723] using wordTrace_append hprefix tailTrace_1318723
  have hstable : (prefixWord ++ tailWord_1318723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318723).length < 2 ^ (prefixWord ++ tailWord_1318723).sum := by decide
  have hdescent : baseEnd_1318723 < baseStart_1318723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318753 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 2, 3]
def baseStart_1318753 : Nat := 118140960795 + 1318753 * 2 ^ 59
def prefixEnd_1318753 : Nat := 4983230072969 + 3 ^ 40 * 1318753 * 2
def baseEnd_1318753 : Nat := 451436102372522737681781

theorem tailTrace_1318753 : CollatzResearch.WordTrace tailWord_1318753 prefixEnd_1318753 451436102372522737681781 := by
  unfold tailWord_1318753
  simp only [CollatzResearch.WordTrace]
  refine ⟨48098873391390580926424913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32065915594260387284283275 48098873391390580926424913)
  ·
    refine ⟨36074155043542935694818685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48098873391390580926424913 36074155043542935694818685)
    ·
      refine ⟨13527808141328600885557007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36074155043542935694818685 13527808141328600885557007)
      ·
        refine ⟨20291712211992901328335511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13527808141328600885557007 20291712211992901328335511)
        ·
          refine ⟨30437568317989351992503267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20291712211992901328335511 30437568317989351992503267)
          ·
            refine ⟨45656352476984027988754901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30437568317989351992503267 45656352476984027988754901)
            ·
              refine ⟨1070070761179313155986443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45656352476984027988754901 1070070761179313155986443)
              ·
                refine ⟨1605106141768969733979665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070070761179313155986443 1605106141768969733979665)
                ·
                  refine ⟨1203829606326727300484749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605106141768969733979665 1203829606326727300484749)
                  ·
                    refine ⟨451436102372522737681781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203829606326727300484749 451436102372522737681781)
                    ·
                      rfl

theorem cell22_1318753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_1318753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318753 prefixEnd_1318753 := by exact prefixLift 1318753
  have htrace : WordTrace (prefixWord ++ tailWord_1318753) baseStart_1318753 baseEnd_1318753 := by
    simpa [prefixWord, tailWord_1318753, baseEnd_1318753] using wordTrace_append hprefix tailTrace_1318753
  have hstable : (prefixWord ++ tailWord_1318753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318753).length < 2 ^ (prefixWord ++ tailWord_1318753).sum := by decide
  have hdescent : baseEnd_1318753 < baseStart_1318753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318766 : List Nat := [4, 1, 2, 3, 1, 2, 1, 8]
def baseStart_1318766 : Nat := 118140960795 + 1318766 * 2 ^ 59
def prefixEnd_1318766 : Nat := 4983230072969 + 3 ^ 40 * 1318766 * 2
def baseEnd_1318766 : Nat := 50160061393132781900749

theorem tailTrace_1318766 : CollatzResearch.WordTrace tailWord_1318766 prefixEnd_1318766 50160061393132781900749 := by
  unfold tailWord_1318766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012418442542935518331019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32066231693562322764432101 6012418442542935518331019)
  ·
    refine ⟨9018627663814403277496529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6012418442542935518331019 9018627663814403277496529)
    ·
      refine ⟨6763970747860802458122397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9018627663814403277496529 6763970747860802458122397)
      ·
        refine ⟨2536489030447800921795899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6763970747860802458122397 2536489030447800921795899)
        ·
          refine ⟨3804733545671701382693849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2536489030447800921795899 3804733545671701382693849)
          ·
            refine ⟨2853550159253776037020387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3804733545671701382693849 2853550159253776037020387)
            ·
              refine ⟨4280325238880664055530581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853550159253776037020387 4280325238880664055530581)
              ·
                refine ⟨50160061393132781900749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4280325238880664055530581 50160061393132781900749)
                ·
                  rfl

theorem cell22_1318766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_1318766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318766 prefixEnd_1318766 := by exact prefixLift 1318766
  have htrace : WordTrace (prefixWord ++ tailWord_1318766) baseStart_1318766 baseEnd_1318766 := by
    simpa [prefixWord, tailWord_1318766, baseEnd_1318766] using wordTrace_append hprefix tailTrace_1318766
  have hstable : (prefixWord ++ tailWord_1318766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318766).length < 2 ^ (prefixWord ++ tailWord_1318766).sum := by decide
  have hdescent : baseEnd_1318766 < baseStart_1318766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318809 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_1318809 : Nat := 118140960795 + 1318809 * 2 ^ 59
def prefixEnd_1318809 : Nat := 4983230072969 + 3 ^ 40 * 1318809 * 2
def baseEnd_1318809 : Nat := 451455272316957258281609

theorem tailTrace_1318809 : CollatzResearch.WordTrace tailWord_1318809 prefixEnd_1318809 451455272316957258281609 := by
  unfold tailWord_1318809
  simp only [CollatzResearch.WordTrace]
  refine ⟨48100915879187702490463481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32067277252791801660308987 48100915879187702490463481)
  ·
    refine ⟨36075686909390776867847611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48100915879187702490463481 36075686909390776867847611)
    ·
      refine ⟨54113530364086165301771417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36075686909390776867847611 54113530364086165301771417)
      ·
        refine ⟨40585147773064623976328563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54113530364086165301771417 40585147773064623976328563)
        ·
          refine ⟨60877721659596935964492845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40585147773064623976328563 60877721659596935964492845)
          ·
            refine ⟨22829145622348850986684817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60877721659596935964492845 22829145622348850986684817)
            ·
              refine ⟨17121859216761638240013613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22829145622348850986684817 17121859216761638240013613)
              ·
                refine ⟨6420697206285614340005105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17121859216761638240013613 6420697206285614340005105)
                ·
                  refine ⟨4815522904714210755003829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6420697206285614340005105 4815522904714210755003829)
                  ·
                    refine ⟨451455272316957258281609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4815522904714210755003829 451455272316957258281609)
                    ·
                      rfl

theorem cell22_1318809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_1318809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318809 prefixEnd_1318809 := by exact prefixLift 1318809
  have htrace : WordTrace (prefixWord ++ tailWord_1318809) baseStart_1318809 baseEnd_1318809 := by
    simpa [prefixWord, tailWord_1318809, baseEnd_1318809] using wordTrace_append hprefix tailTrace_1318809
  have hstable : (prefixWord ++ tailWord_1318809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318809).length < 2 ^ (prefixWord ++ tailWord_1318809).sum := by decide
  have hdescent : baseEnd_1318809 < baseStart_1318809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318871 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 1, 5]
def baseStart_1318871 : Nat := 118140960795 + 1318871 * 2 ^ 59
def prefixEnd_1318871 : Nat := 4983230072969 + 3 ^ 40 * 1318871 * 2
def baseEnd_1318871 : Nat := 451476496184009763231419

theorem tailTrace_1318871 : CollatzResearch.WordTrace tailWord_1318871 prefixEnd_1318871 451476496184009763231419 := by
  unfold tailWord_1318871
  simp only [CollatzResearch.WordTrace]
  refine ⟨48103177204963087079220467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32068784803308724719480311 48103177204963087079220467)
  ·
    refine ⟨72154765807444630618830701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48103177204963087079220467 72154765807444630618830701)
    ·
      refine ⟨27058037177791736482061513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72154765807444630618830701 27058037177791736482061513)
      ·
        refine ⟨20293527883343802361546135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27058037177791736482061513 20293527883343802361546135)
        ·
          refine ⟨30440291825015703542319203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20293527883343802361546135 30440291825015703542319203)
          ·
            refine ⟨45660437737523555313478805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30440291825015703542319203 45660437737523555313478805)
            ·
              refine ⟨2140333018946416655319319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45660437737523555313478805 2140333018946416655319319)
              ·
                refine ⟨3210499528419624982978979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140333018946416655319319 3210499528419624982978979)
                ·
                  refine ⟨4815749292629437474468469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210499528419624982978979 4815749292629437474468469)
                  ·
                    refine ⟨451476496184009763231419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4815749292629437474468469 451476496184009763231419)
                    ·
                      rfl

theorem cell22_1318871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_1318871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318871 prefixEnd_1318871 := by exact prefixLift 1318871
  have htrace : WordTrace (prefixWord ++ tailWord_1318871) baseStart_1318871 baseEnd_1318871 := by
    simpa [prefixWord, tailWord_1318871, baseEnd_1318871] using wordTrace_append hprefix tailTrace_1318871
  have hstable : (prefixWord ++ tailWord_1318871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318871).length < 2 ^ (prefixWord ++ tailWord_1318871).sum := by decide
  have hdescent : baseEnd_1318871 < baseStart_1318871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318899 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 9]
def baseStart_1318899 : Nat := 118140960795 + 1318899 * 2 ^ 59
def prefixEnd_1318899 : Nat := 4983230072969 + 3 ^ 40 * 1318899 * 2
def baseEnd_1318899 : Nat := 451486081156227023531333

theorem tailTrace_1318899 : CollatzResearch.WordTrace tailWord_1318899 prefixEnd_1318899 451486081156227023531333 := by
  unfold tailWord_1318899
  simp only [CollatzResearch.WordTrace]
  refine ⟨48104198448861647861239751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32069465632574431907493167 48104198448861647861239751)
  ·
    refine ⟨72156297673292471791859627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48104198448861647861239751 72156297673292471791859627)
    ·
      refine ⟨108234446509938707687789441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72156297673292471791859627 108234446509938707687789441)
      ·
        refine ⟨81175834882454030765842081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108234446509938707687789441 81175834882454030765842081)
        ·
          refine ⟨60881876161840523074381561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81175834882454030765842081 60881876161840523074381561)
          ·
            refine ⟨45661407121380392305786171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60881876161840523074381561 45661407121380392305786171)
            ·
              refine ⟨68492110682070588458679257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45661407121380392305786171 68492110682070588458679257)
              ·
                refine ⟨51369083011552941344009443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68492110682070588458679257 51369083011552941344009443)
                ·
                  refine ⟨77053624517329412016014165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51369083011552941344009443 77053624517329412016014165)
                  ·
                    refine ⟨451486081156227023531333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 77053624517329412016014165 451486081156227023531333)
                    ·
                      rfl

theorem cell22_1318899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_1318899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318899 prefixEnd_1318899 := by exact prefixLift 1318899
  have htrace : WordTrace (prefixWord ++ tailWord_1318899) baseStart_1318899 baseEnd_1318899 := by
    simpa [prefixWord, tailWord_1318899, baseEnd_1318899] using wordTrace_append hprefix tailTrace_1318899
  have hstable : (prefixWord ++ tailWord_1318899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318899).length < 2 ^ (prefixWord ++ tailWord_1318899).sum := by decide
  have hdescent : baseEnd_1318899 < baseStart_1318899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318905 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 2, 3]
def baseStart_1318905 : Nat := 118140960795 + 1318905 * 2 ^ 59
def prefixEnd_1318905 : Nat := 4983230072969 + 3 ^ 40 * 1318905 * 2
def baseEnd_1318905 : Nat := 451488135078845007881315

theorem tailTrace_1318905 : CollatzResearch.WordTrace tailWord_1318905 prefixEnd_1318905 451488135078845007881315 := by
  unfold tailWord_1318905
  simp only [CollatzResearch.WordTrace]
  refine ⟨48104417286839910885958169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32069611524559940590638779 48104417286839910885958169)
  ·
    refine ⟨36078312965129933164468627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48104417286839910885958169 36078312965129933164468627)
    ·
      refine ⟨54117469447694899746702941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36078312965129933164468627 54117469447694899746702941)
      ·
        refine ⟨20294051042885587405013603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54117469447694899746702941 20294051042885587405013603)
        ·
          refine ⟨30441076564328381107520405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20294051042885587405013603 30441076564328381107520405)
          ·
            refine ⟨1426925463952892864415019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30441076564328381107520405 1426925463952892864415019)
            ·
              refine ⟨2140388195929339296622529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426925463952892864415019 2140388195929339296622529)
              ·
                refine ⟨1605291146947004472466897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140388195929339296622529 1605291146947004472466897)
                ·
                  refine ⟨1203968360210253354350173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605291146947004472466897 1203968360210253354350173)
                  ·
                    refine ⟨451488135078845007881315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203968360210253354350173 451488135078845007881315)
                    ·
                      rfl

theorem cell22_1318905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_1318905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318905 prefixEnd_1318905 := by exact prefixLift 1318905
  have htrace : WordTrace (prefixWord ++ tailWord_1318905) baseStart_1318905 baseEnd_1318905 := by
    simpa [prefixWord, tailWord_1318905, baseEnd_1318905] using wordTrace_append hprefix tailTrace_1318905
  have hstable : (prefixWord ++ tailWord_1318905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318905).length < 2 ^ (prefixWord ++ tailWord_1318905).sum := by decide
  have hdescent : baseEnd_1318905 < baseStart_1318905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318922 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_1318922 : Nat := 118140960795 + 1318922 * 2 ^ 59
def prefixEnd_1318922 : Nat := 4983230072969 + 3 ^ 40 * 1318922 * 2
def baseEnd_1318922 : Nat := 451493954526262630206263

theorem tailTrace_1318922 : CollatzResearch.WordTrace tailWord_1318922 prefixEnd_1318922 451493954526262630206263 := by
  unfold tailWord_1318922
  simp only [CollatzResearch.WordTrace]
  refine ⟨12026259331944580697331755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32070024885185548526218013 12026259331944580697331755)
  ·
    refine ⟨18039388997916871045997633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12026259331944580697331755 18039388997916871045997633)
    ·
      refine ⟨13529541748437653284498225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18039388997916871045997633 13529541748437653284498225)
      ·
        refine ⟨10147156311328239963373669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13529541748437653284498225 10147156311328239963373669)
        ·
          refine ⟨1902591808374044993132563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10147156311328239963373669 1902591808374044993132563)
          ·
            refine ⟨2853887712561067489698845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902591808374044993132563 2853887712561067489698845)
            ·
              refine ⟨1070207892210400308637067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2853887712561067489698845 1070207892210400308637067)
              ·
                refine ⟨1605311838315600462955601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070207892210400308637067 1605311838315600462955601)
                ·
                  refine ⟨1203983878736700347216701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605311838315600462955601 1203983878736700347216701)
                  ·
                    refine ⟨451493954526262630206263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203983878736700347216701 451493954526262630206263)
                    ·
                      rfl

theorem cell22_1318922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_1318922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318922 prefixEnd_1318922 := by exact prefixLift 1318922
  have htrace : WordTrace (prefixWord ++ tailWord_1318922) baseStart_1318922 baseEnd_1318922 := by
    simpa [prefixWord, tailWord_1318922, baseEnd_1318922] using wordTrace_append hprefix tailTrace_1318922
  have hstable : (prefixWord ++ tailWord_1318922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318922).length < 2 ^ (prefixWord ++ tailWord_1318922).sum := by decide
  have hdescent : baseEnd_1318922 < baseStart_1318922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318935 : List Nat := [1, 1, 3, 5, 2, 2, 2, 6]
def baseStart_1318935 : Nat := 118140960795 + 1318935 * 2 ^ 59
def prefixEnd_1318935 : Nat := 4983230072969 + 3 ^ 40 * 1318935 * 2
def baseEnd_1318935 : Nat := 50166489410214992181247

theorem tailTrace_1318935 : CollatzResearch.WordTrace tailWord_1318935 prefixEnd_1318935 50166489410214992181247 := by
  unfold tailWord_1318935
  simp only [CollatzResearch.WordTrace]
  refine ⟨48105511476731226009550259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32070340984487484006366839 48105511476731226009550259)
  ·
    refine ⟨72158267215096839014325389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48105511476731226009550259 72158267215096839014325389)
    ·
      refine ⟨27059350205661314630372021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72158267215096839014325389 27059350205661314630372021)
      ·
        refine ⟨2536814081780748246597377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27059350205661314630372021 2536814081780748246597377)
        ·
          refine ⟨1902610561335561184948033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2536814081780748246597377 1902610561335561184948033)
          ·
            refine ⟨1426957921001670888711025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1902610561335561184948033 1426957921001670888711025)
            ·
              refine ⟨1070218440751253166533269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1426957921001670888711025 1070218440751253166533269)
              ·
                refine ⟨50166489410214992181247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1070218440751253166533269 50166489410214992181247)
                ·
                  rfl

theorem cell22_1318935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 6].length) (baseStart_1318935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318935 prefixEnd_1318935 := by exact prefixLift 1318935
  have htrace : WordTrace (prefixWord ++ tailWord_1318935) baseStart_1318935 baseEnd_1318935 := by
    simpa [prefixWord, tailWord_1318935, baseEnd_1318935] using wordTrace_append hprefix tailTrace_1318935
  have hstable : (prefixWord ++ tailWord_1318935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318935).length < 2 ^ (prefixWord ++ tailWord_1318935).sum := by decide
  have hdescent : baseEnd_1318935 < baseStart_1318935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318946 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1318946 : Nat := 118140960795 + 1318946 * 2 ^ 59
def prefixEnd_1318946 : Nat := 4983230072969 + 3 ^ 40 * 1318946 * 2
def baseEnd_1318946 : Nat := 150500723405578189202063

theorem tailTrace_1318946 : CollatzResearch.WordTrace tailWord_1318946 prefixEnd_1318946 150500723405578189202063 := by
  unfold tailWord_1318946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12026478169922843722050173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32070608453127583258800461 12026478169922843722050173)
  ·
    refine ⟨4509929313721066395768815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12026478169922843722050173 4509929313721066395768815)
    ·
      refine ⟨6764893970581599593653223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4509929313721066395768815 6764893970581599593653223)
      ·
        refine ⟨10147340955872399390479835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6764893970581599593653223 10147340955872399390479835)
        ·
          refine ⟨15221011433808599085719753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10147340955872399390479835 15221011433808599085719753)
          ·
            refine ⟨11415758575356449314289815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15221011433808599085719753 11415758575356449314289815)
            ·
              refine ⟨17123637863034673971434723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11415758575356449314289815 17123637863034673971434723)
              ·
                refine ⟨25685456794552010957152085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17123637863034673971434723 25685456794552010957152085)
                ·
                  refine ⟨150500723405578189202063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25685456794552010957152085 150500723405578189202063)
                  ·
                    rfl

theorem cell22_1318946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1318946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1318946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1318946 prefixEnd_1318946 := by exact prefixLift 1318946
  have htrace : WordTrace (prefixWord ++ tailWord_1318946) baseStart_1318946 baseEnd_1318946 := by
    simpa [prefixWord, tailWord_1318946, baseEnd_1318946] using wordTrace_append hprefix tailTrace_1318946
  have hstable : (prefixWord ++ tailWord_1318946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318946).length < 2 ^ (prefixWord ++ tailWord_1318946).sum := by decide
  have hdescent : baseEnd_1318946 < baseStart_1318946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319070 : List Nat := [4, 3, 1, 1, 3, 1, 9]
def baseStart_1319070 : Nat := 118140960795 + 1319070 * 2 ^ 59
def prefixEnd_1319070 : Nat := 4983230072969 + 3 ^ 40 * 1319070 * 2
def baseEnd_1319070 : Nat := 16723874738919984352067

theorem tailTrace_1319070 : CollatzResearch.WordTrace tailWord_1319070 prefixEnd_1319070 16723874738919984352067 := by
  unfold tailWord_1319070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6013804416405268008214333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32073623554161429377143109 6013804416405268008214333)
  ·
    refine ⟨2255176656151975503080375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6013804416405268008214333 2255176656151975503080375)
    ·
      refine ⟨3382764984227963254620563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255176656151975503080375 3382764984227963254620563)
      ·
        refine ⟨5074147476341944881930845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3382764984227963254620563 5074147476341944881930845)
        ·
          refine ⟨1902805303628229330724067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5074147476341944881930845 1902805303628229330724067)
          ·
            refine ⟨2854207955442343996086101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902805303628229330724067 2854207955442343996086101)
            ·
              refine ⟨16723874738919984352067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2854207955442343996086101 16723874738919984352067)
              ·
                rfl

theorem cell22_1319070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 9].length) (baseStart_1319070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319070 prefixEnd_1319070 := by exact prefixLift 1319070
  have htrace : WordTrace (prefixWord ++ tailWord_1319070) baseStart_1319070 baseEnd_1319070 := by
    simpa [prefixWord, tailWord_1319070, baseEnd_1319070] using wordTrace_append hprefix tailTrace_1319070
  have hstable : (prefixWord ++ tailWord_1319070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319070).length < 2 ^ (prefixWord ++ tailWord_1319070).sum := by decide
  have hdescent : baseEnd_1319070 < baseStart_1319070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319074 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_1319074 : Nat := 118140960795 + 1319074 * 2 ^ 59
def prefixEnd_1319074 : Nat := 4983230072969 + 3 ^ 40 * 1319074 * 2
def baseEnd_1319074 : Nat := 451545987232584900405797

theorem tailTrace_1319074 : CollatzResearch.WordTrace tailWord_1319074 prefixEnd_1319074 451545987232584900405797 := by
  unfold tailWord_1319074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027645305806913187215069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32073720815485101832573517 12027645305806913187215069)
  ·
    refine ⟨4510366989677592445205651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12027645305806913187215069 4510366989677592445205651)
    ·
      refine ⟨6765550484516388667808477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4510366989677592445205651 6765550484516388667808477)
      ·
        refine ⟨2537081431693645750428179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6765550484516388667808477 2537081431693645750428179)
        ·
          refine ⟨3805622147540468625642269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537081431693645750428179 3805622147540468625642269)
          ·
            refine ⟨1427108305327675734615851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3805622147540468625642269 1427108305327675734615851)
            ·
              refine ⟨2140662457991513601923777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427108305327675734615851 2140662457991513601923777)
              ·
                refine ⟨1605496843493635201442833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140662457991513601923777 1605496843493635201442833)
                ·
                  refine ⟨1204122632620226401082125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605496843493635201442833 1204122632620226401082125)
                  ·
                    refine ⟨451545987232584900405797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204122632620226401082125 451545987232584900405797)
                    ·
                      rfl

theorem cell22_1319074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_1319074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319074 prefixEnd_1319074 := by exact prefixLift 1319074
  have htrace : WordTrace (prefixWord ++ tailWord_1319074) baseStart_1319074 baseEnd_1319074 := by
    simpa [prefixWord, tailWord_1319074, baseEnd_1319074] using wordTrace_append hprefix tailTrace_1319074
  have hstable : (prefixWord ++ tailWord_1319074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319074).length < 2 ^ (prefixWord ++ tailWord_1319074).sum := by decide
  have hdescent : baseEnd_1319074 < baseStart_1319074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319098 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_1319098 : Nat := 118140960795 + 1319098 * 2 ^ 59
def prefixEnd_1319098 : Nat := 4983230072969 + 3 ^ 40 * 1319098 * 2
def baseEnd_1319098 : Nat := 150518067641018945935241

theorem tailTrace_1319098 : CollatzResearch.WordTrace tailWord_1319098 prefixEnd_1319098 150518067641018945935241 := by
  unfold tailWord_1319098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027864143785176211933487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32074304383427136565155965 12027864143785176211933487)
  ·
    refine ⟨18041796215677764317900231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12027864143785176211933487 18041796215677764317900231)
    ·
      refine ⟨27062694323516646476850347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18041796215677764317900231 27062694323516646476850347)
      ·
        refine ⟨40594041485274969715275521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27062694323516646476850347 40594041485274969715275521)
        ·
          refine ⟨30445531113956227286456641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40594041485274969715275521 30445531113956227286456641)
          ·
            refine ⟨22834148335467170464842481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30445531113956227286456641 22834148335467170464842481)
            ·
              refine ⟨17125611251600377848631861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22834148335467170464842481 17125611251600377848631861)
              ·
                refine ⟨1605526054837535423309237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17125611251600377848631861 1605526054837535423309237)
                ·
                  refine ⟨150518067641018945935241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605526054837535423309237 150518067641018945935241)
                  ·
                    rfl

theorem cell22_1319098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_1319098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319098 prefixEnd_1319098 := by exact prefixLift 1319098
  have htrace : WordTrace (prefixWord ++ tailWord_1319098) baseStart_1319098 baseEnd_1319098 := by
    simpa [prefixWord, tailWord_1319098, baseEnd_1319098] using wordTrace_append hprefix tailTrace_1319098
  have hstable : (prefixWord ++ tailWord_1319098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319098).length < 2 ^ (prefixWord ++ tailWord_1319098).sum := by decide
  have hdescent : baseEnd_1319098 < baseStart_1319098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319149 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1319149 : Nat := 118140960795 + 1319149 * 2 ^ 59
def prefixEnd_1319149 : Nat := 4983230072969 + 3 ^ 40 * 1319149 * 2
def baseEnd_1319149 : Nat := 150523887088436568260189

theorem tailTrace_1319149 : CollatzResearch.WordTrace tailWord_1319149 prefixEnd_1319149 150523887088436568260189 := by
  unfold tailWord_1319149
  simp only [CollatzResearch.WordTrace]
  refine ⟨48113316697955940557840501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32075544465303960371893667 48113316697955940557840501)
  ·
    refine ⟨4510623440433369427297547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48113316697955940557840501 4510623440433369427297547)
    ·
      refine ⟨6765935160650054140946321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4510623440433369427297547 6765935160650054140946321)
      ·
        refine ⟨5074451370487540605709741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6765935160650054140946321 5074451370487540605709741)
        ·
          refine ⟨1902919263932827727141153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5074451370487540605709741 1902919263932827727141153)
          ·
            refine ⟨1427189447949620795355865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1902919263932827727141153 1427189447949620795355865)
            ·
              refine ⟨1070392085962215596516899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1427189447949620795355865 1070392085962215596516899)
              ·
                refine ⟨1605588128943323394775349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070392085962215596516899 1605588128943323394775349)
                ·
                  refine ⟨150523887088436568260189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605588128943323394775349 150523887088436568260189)
                  ·
                    rfl

theorem cell22_1319149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1319149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319149 prefixEnd_1319149 := by exact prefixLift 1319149
  have htrace : WordTrace (prefixWord ++ tailWord_1319149) baseStart_1319149 baseEnd_1319149 := by
    simpa [prefixWord, tailWord_1319149, baseEnd_1319149] using wordTrace_append hprefix tailTrace_1319149
  have hstable : (prefixWord ++ tailWord_1319149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319149).length < 2 ^ (prefixWord ++ tailWord_1319149).sum := by decide
  have hdescent : baseEnd_1319149 < baseStart_1319149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319162 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_1319162 : Nat := 118140960795 + 1319162 * 2 ^ 59
def prefixEnd_1319162 : Nat := 4983230072969 + 3 ^ 40 * 1319162 * 2
def baseEnd_1319162 : Nat := 451576111430982004205527

theorem tailTrace_1319162 : CollatzResearch.WordTrace tailWord_1319162 prefixEnd_1319162 451576111430982004205527 := by
  unfold tailWord_1319162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12028447711727210944515935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32075860564605895852042493 12028447711727210944515935)
  ·
    refine ⟨18042671567590816416773903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12028447711727210944515935 18042671567590816416773903)
    ·
      refine ⟨27064007351386224625160855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18042671567590816416773903 27064007351386224625160855)
      ·
        refine ⟨40596011027079336937741283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27064007351386224625160855 40596011027079336937741283)
        ·
          refine ⟨60894016540619005406611925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40596011027079336937741283 60894016540619005406611925)
          ·
            refine ⟨1427203512670757939217467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60894016540619005406611925 1427203512670757939217467)
            ·
              refine ⟨2140805269006136908826201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427203512670757939217467 2140805269006136908826201)
              ·
                refine ⟨1605603951754602681619651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140805269006136908826201 1605603951754602681619651)
                ·
                  refine ⟨2408405927631904022429477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605603951754602681619651 2408405927631904022429477)
                  ·
                    refine ⟨451576111430982004205527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2408405927631904022429477 451576111430982004205527)
                    ·
                      rfl

theorem cell22_1319162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_1319162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319162 prefixEnd_1319162 := by exact prefixLift 1319162
  have htrace : WordTrace (prefixWord ++ tailWord_1319162) baseStart_1319162 baseEnd_1319162 := by
    simpa [prefixWord, tailWord_1319162, baseEnd_1319162] using wordTrace_append hprefix tailTrace_1319162
  have hstable : (prefixWord ++ tailWord_1319162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319162).length < 2 ^ (prefixWord ++ tailWord_1319162).sum := by decide
  have hdescent : baseEnd_1319162 < baseStart_1319162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319192 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1319192 : Nat := 118140960795 + 1319192 * 2 ^ 59
def prefixEnd_1319192 : Nat := 4983230072969 + 3 ^ 40 * 1319192 * 2
def baseEnd_1319192 : Nat := 451586381044071925955435

theorem tailTrace_1319192 : CollatzResearch.WordTrace tailWord_1319192 prefixEnd_1319192 451586381044071925955435 := by
  unfold tailWord_1319192
  simp only [CollatzResearch.WordTrace]
  refine ⟨24057442518400079450827915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32076590024533439267770553 24057442518400079450827915)
  ·
    refine ⟨36086163777600119176241873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24057442518400079450827915 36086163777600119176241873)
    ·
      refine ⟨27064622833200089382181405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36086163777600119176241873 27064622833200089382181405)
      ·
        refine ⟨10149233562450033518318027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27064622833200089382181405 10149233562450033518318027)
        ·
          refine ⟨15223850343675050277477041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10149233562450033518318027 15223850343675050277477041)
          ·
            refine ⟨11417887757756287708107781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15223850343675050277477041 11417887757756287708107781)
            ·
              refine ⟨2140853954579303945270209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11417887757756287708107781 2140853954579303945270209)
              ·
                refine ⟨1605640465934477958952657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140853954579303945270209 1605640465934477958952657)
                ·
                  refine ⟨1204230349450858469214493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605640465934477958952657 1204230349450858469214493)
                  ·
                    refine ⟨451586381044071925955435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204230349450858469214493 451586381044071925955435)
                    ·
                      rfl

theorem cell22_1319192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1319192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319192 prefixEnd_1319192 := by exact prefixLift 1319192
  have htrace : WordTrace (prefixWord ++ tailWord_1319192) baseStart_1319192 baseEnd_1319192 := by
    simpa [prefixWord, tailWord_1319192, baseEnd_1319192] using wordTrace_append hprefix tailTrace_1319192
  have hstable : (prefixWord ++ tailWord_1319192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319192).length < 2 ^ (prefixWord ++ tailWord_1319192).sum := by decide
  have hdescent : baseEnd_1319192 < baseStart_1319192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319267 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 5]
def baseStart_1319267 : Nat := 118140960795 + 1319267 * 2 ^ 59
def prefixEnd_1319267 : Nat := 4983230072969 + 3 ^ 40 * 1319267 * 2
def baseEnd_1319267 : Nat := 150537351692265576776735

theorem tailTrace_1319267 : CollatzResearch.WordTrace tailWord_1319267 prefixEnd_1319267 150537351692265576776735 := by
  unfold tailWord_1319267
  simp only [CollatzResearch.WordTrace]
  refine ⟨48117620511528446710636055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32078413674352297807090703 48117620511528446710636055)
  ·
    refine ⟨72176430767292670065954083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48117620511528446710636055 72176430767292670065954083)
    ·
      refine ⟨108264646150939005098931125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72176430767292670065954083 108264646150939005098931125)
      ·
        refine ⟨10149810576650531728024793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108264646150939005098931125 10149810576650531728024793)
        ·
          refine ⟨7612357932487898796018595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10149810576650531728024793 7612357932487898796018595)
          ·
            refine ⟨11418536898731848194027893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612357932487898796018595 11418536898731848194027893)
            ·
              refine ⟨1070487834256110768190115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11418536898731848194027893 1070487834256110768190115)
              ·
                refine ⟨1605731751384166152285173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070487834256110768190115 1605731751384166152285173)
                ·
                  refine ⟨150537351692265576776735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605731751384166152285173 150537351692265576776735)
                  ·
                    rfl

theorem cell22_1319267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 5].length) (baseStart_1319267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319267 prefixEnd_1319267 := by exact prefixLift 1319267
  have htrace : WordTrace (prefixWord ++ tailWord_1319267) baseStart_1319267 baseEnd_1319267 := by
    simpa [prefixWord, tailWord_1319267, baseEnd_1319267] using wordTrace_append hprefix tailTrace_1319267
  have hstable : (prefixWord ++ tailWord_1319267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319267).length < 2 ^ (prefixWord ++ tailWord_1319267).sum := by decide
  have hdescent : baseEnd_1319267 < baseStart_1319267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319318 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1319318 : Nat := 118140960795 + 1319318 * 2 ^ 59
def prefixEnd_1319318 : Nat := 4983230072969 + 3 ^ 40 * 1319318 * 2
def baseEnd_1319318 : Nat := 150543171139683199101683

theorem tailTrace_1319318 : CollatzResearch.WordTrace tailWord_1319318 prefixEnd_1319318 150543171139683199101683 := by
  unfold tailWord_1319318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007467539646480151296413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32079653756229121613828405 3007467539646480151296413)
  ·
    refine ⟨1127800327367430056736155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3007467539646480151296413 1127800327367430056736155)
    ·
      refine ⟨1691700491051145085104233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127800327367430056736155 1691700491051145085104233)
      ·
        refine ⟨1268775368288358813828175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1691700491051145085104233 1268775368288358813828175)
        ·
          refine ⟨1903163052432538220742263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268775368288358813828175 1903163052432538220742263)
          ·
            refine ⟨2854744578648807331113395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903163052432538220742263 2854744578648807331113395)
            ·
              refine ⟨4282116867973210996670093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854744578648807331113395 4282116867973210996670093)
              ·
                refine ⟨1605793825489954123751285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4282116867973210996670093 1605793825489954123751285)
                ·
                  refine ⟨150543171139683199101683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605793825489954123751285 150543171139683199101683)
                  ·
                    rfl

theorem cell22_1319318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1319318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319318 prefixEnd_1319318 := by exact prefixLift 1319318
  have htrace : WordTrace (prefixWord ++ tailWord_1319318) baseStart_1319318 baseEnd_1319318 := by
    simpa [prefixWord, tailWord_1319318, baseEnd_1319318] using wordTrace_append hprefix tailTrace_1319318
  have hstable : (prefixWord ++ tailWord_1319318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319318).length < 2 ^ (prefixWord ++ tailWord_1319318).sum := by decide
  have hdescent : baseEnd_1319318 < baseStart_1319318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319370 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1319370 : Nat := 118140960795 + 1319370 * 2 ^ 59
def prefixEnd_1319370 : Nat := 4983230072969 + 3 ^ 40 * 1319370 * 2
def baseEnd_1319370 : Nat := 451647314081738795004889

theorem tailTrace_1319370 : CollatzResearch.WordTrace tailWord_1319370 prefixEnd_1319370 451647314081738795004889 := by
  unfold tailWord_1319370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030344307538823825408891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32080918153436863534423709 12030344307538823825408891)
  ·
    refine ⟨18045516461308235738113337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12030344307538823825408891 18045516461308235738113337)
    ·
      refine ⟨13534137345981176803585003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18045516461308235738113337 13534137345981176803585003)
      ·
        refine ⟨20301206018971765205377505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13534137345981176803585003 20301206018971765205377505)
        ·
          refine ⟨15225904514228823904033129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20301206018971765205377505 15225904514228823904033129)
          ·
            refine ⟨11419428385671617928024847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15225904514228823904033129 11419428385671617928024847)
            ·
              refine ⟨17129142578507426892037271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11419428385671617928024847 17129142578507426892037271)
              ·
                refine ⟨25693713867761140338055907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17129142578507426892037271 25693713867761140338055907)
                ·
                  refine ⟨38540570801641710507083861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25693713867761140338055907 38540570801641710507083861)
                  ·
                    refine ⟨451647314081738795004889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38540570801641710507083861 451647314081738795004889)
                    ·
                      rfl

theorem cell22_1319370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1319370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319370 prefixEnd_1319370 := by exact prefixLift 1319370
  have htrace : WordTrace (prefixWord ++ tailWord_1319370) baseStart_1319370 baseEnd_1319370 := by
    simpa [prefixWord, tailWord_1319370, baseEnd_1319370] using wordTrace_append hprefix tailTrace_1319370
  have hstable : (prefixWord ++ tailWord_1319370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319370).length < 2 ^ (prefixWord ++ tailWord_1319370).sum := by decide
  have hdescent : baseEnd_1319370 < baseStart_1319370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319389 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1319389 : Nat := 118140960795 + 1319389 * 2 ^ 59
def prefixEnd_1319389 : Nat := 4983230072969 + 3 ^ 40 * 1319389 * 2
def baseEnd_1319389 : Nat := 451653818170029078779831

theorem tailTrace_1319389 : CollatzResearch.WordTrace tailWord_1319389 prefixEnd_1319389 451653818170029078779831 := by
  unfold tailWord_1319389
  simp only [CollatzResearch.WordTrace]
  refine ⟨48122070217086461546577221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32081380144724307697718147 48122070217086461546577221)
  ·
    refine ⟨9022888165703711539983229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48122070217086461546577221 9022888165703711539983229)
    ·
      refine ⟨3383583062138891827493711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9022888165703711539983229 3383583062138891827493711)
      ·
        refine ⟨5075374593208337741240567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383583062138891827493711 5075374593208337741240567)
        ·
          refine ⟨7613061889812506611860851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075374593208337741240567 7613061889812506611860851)
          ·
            refine ⟨11419592834718759917791277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613061889812506611860851 11419592834718759917791277)
            ·
              refine ⟨4282347313019534969171729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11419592834718759917791277 4282347313019534969171729)
              ·
                refine ⟨3211760484764651226878797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282347313019534969171729 3211760484764651226878797)
                ·
                  refine ⟨1204410181786744210079549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3211760484764651226878797 1204410181786744210079549)
                  ·
                    refine ⟨451653818170029078779831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204410181786744210079549 451653818170029078779831)
                    ·
                      rfl

theorem cell22_1319389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1319389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319389 prefixEnd_1319389 := by exact prefixLift 1319389
  have htrace : WordTrace (prefixWord ++ tailWord_1319389) baseStart_1319389 baseEnd_1319389 := by
    simpa [prefixWord, tailWord_1319389, baseEnd_1319389] using wordTrace_append hprefix tailTrace_1319389
  have hstable : (prefixWord ++ tailWord_1319389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319389).length < 2 ^ (prefixWord ++ tailWord_1319389).sum := by decide
  have hdescent : baseEnd_1319389 < baseStart_1319389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319406 : List Nat := [4, 1, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_1319406 : Nat := 118140960795 + 1319406 * 2 ^ 59
def prefixEnd_1319406 : Nat := 4983230072969 + 3 ^ 40 * 1319406 * 2
def baseEnd_1319406 : Nat := 451659637617446701104779

theorem tailTrace_1319406 : CollatzResearch.WordTrace tailWord_1319406 prefixEnd_1319406 451659637617446701104779 := by
  unfold tailWord_1319406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015336282253109181243259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32081793505349915633297381 6015336282253109181243259)
  ·
    refine ⟨9023004423379663771864889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015336282253109181243259 9023004423379663771864889)
    ·
      refine ⟨6767253317534747828898667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9023004423379663771864889 6767253317534747828898667)
      ·
        refine ⟨10150879976302121743348001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6767253317534747828898667 10150879976302121743348001)
        ·
          refine ⟨7613159982226591307511001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10150879976302121743348001 7613159982226591307511001)
          ·
            refine ⟨5709869986669943480633251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7613159982226591307511001 5709869986669943480633251)
            ·
              refine ⟨8564804980004915220949877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5709869986669943480633251 8564804980004915220949877)
              ·
                refine ⟨802950466875460801964051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8564804980004915220949877 802950466875460801964051)
                ·
                  refine ⟨1204425700313191202946077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802950466875460801964051 1204425700313191202946077)
                  ·
                    refine ⟨451659637617446701104779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204425700313191202946077 451659637617446701104779)
                    ·
                      rfl

theorem cell22_1319406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_1319406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319406 prefixEnd_1319406 := by exact prefixLift 1319406
  have htrace : WordTrace (prefixWord ++ tailWord_1319406) baseStart_1319406 baseEnd_1319406 := by
    simpa [prefixWord, tailWord_1319406, baseEnd_1319406] using wordTrace_append hprefix tailTrace_1319406
  have hstable : (prefixWord ++ tailWord_1319406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319406).length < 2 ^ (prefixWord ++ tailWord_1319406).sum := by decide
  have hdescent : baseEnd_1319406 < baseStart_1319406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319479 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 2, 3]
def baseStart_1319479 : Nat := 118140960795 + 1319479 * 2 ^ 59
def prefixEnd_1319479 : Nat := 4983230072969 + 3 ^ 40 * 1319479 * 2
def baseEnd_1319479 : Nat := 451684627009298844029555

theorem tailTrace_1319479 : CollatzResearch.WordTrace tailWord_1319479 prefixEnd_1319479 451684627009298844029555 := by
  unfold tailWord_1319479
  simp only [CollatzResearch.WordTrace]
  refine ⟨48125352786760406917353491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32083568524506937944902327 48125352786760406917353491)
  ·
    refine ⟨72188029180140610376030237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48125352786760406917353491 72188029180140610376030237)
    ·
      refine ⟨27070510942552728891011339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72188029180140610376030237 27070510942552728891011339)
      ·
        refine ⟨40605766413829093336517009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27070510942552728891011339 40605766413829093336517009)
        ·
          refine ⟨30454324810371820002387757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40605766413829093336517009 30454324810371820002387757)
          ·
            refine ⟨11420371803889432500895409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30454324810371820002387757 11420371803889432500895409)
            ·
              refine ⟨8565278852917074375671557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11420371803889432500895409 8565278852917074375671557)
              ·
                refine ⟨1605989784921951445438417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8565278852917074375671557 1605989784921951445438417)
                ·
                  refine ⟨1204492338691463584078813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605989784921951445438417 1204492338691463584078813)
                  ·
                    refine ⟨451684627009298844029555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204492338691463584078813 451684627009298844029555)
                    ·
                      rfl

theorem cell22_1319479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_1319479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319479 prefixEnd_1319479 := by exact prefixLift 1319479
  have htrace : WordTrace (prefixWord ++ tailWord_1319479) baseStart_1319479 baseEnd_1319479 := by
    simpa [prefixWord, tailWord_1319479, baseEnd_1319479] using wordTrace_append hprefix tailTrace_1319479
  have hstable : (prefixWord ++ tailWord_1319479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319479).length < 2 ^ (prefixWord ++ tailWord_1319479).sum := by decide
  have hdescent : baseEnd_1319479 < baseStart_1319479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319481 : List Nat := [1, 2, 1, 5, 1, 1, 5, 2, 4]
def baseStart_1319481 : Nat := 118140960795 + 1319481 * 2 ^ 59
def prefixEnd_1319481 : Nat := 4983230072969 + 3 ^ 40 * 1319481 * 2
def baseEnd_1319481 : Nat := 150561770550057168493183

theorem tailTrace_1319481 : CollatzResearch.WordTrace tailWord_1319481 prefixEnd_1319481 150561770550057168493183 := by
  unfold tailWord_1319481
  simp only [CollatzResearch.WordTrace]
  refine ⟨48125425732753161258926297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32083617155168774172617531 48125425732753161258926297)
  ·
    refine ⟨36094069299564870944194723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48125425732753161258926297 36094069299564870944194723)
    ·
      refine ⟨54141103949347306416292085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36094069299564870944194723 54141103949347306416292085)
      ·
        refine ⟨5075728495251309976527383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54141103949347306416292085 5075728495251309976527383)
        ·
          refine ⟨7613592742876964964791075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075728495251309976527383 7613592742876964964791075)
          ·
            refine ⟨11420389114315447447186613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613592742876964964791075 11420389114315447447186613)
            ·
              refine ⟨1070661479467073198173745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11420389114315447447186613 1070661479467073198173745)
              ·
                refine ⟨802996109600304898630309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070661479467073198173745 802996109600304898630309)
                ·
                  refine ⟨150561770550057168493183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802996109600304898630309 150561770550057168493183)
                  ·
                    rfl

theorem cell22_1319481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_1319481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319481 prefixEnd_1319481 := by exact prefixLift 1319481
  have htrace : WordTrace (prefixWord ++ tailWord_1319481) baseStart_1319481 baseEnd_1319481 := by
    simpa [prefixWord, tailWord_1319481, baseEnd_1319481] using wordTrace_append hprefix tailTrace_1319481
  have hstable : (prefixWord ++ tailWord_1319481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319481).length < 2 ^ (prefixWord ++ tailWord_1319481).sum := by decide
  have hdescent : baseEnd_1319481 < baseStart_1319481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319552 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_1319552 : Nat := 118140960795 + 1319552 * 2 ^ 59
def prefixEnd_1319552 : Nat := 4983230072969 + 3 ^ 40 * 1319552 * 2
def baseEnd_1319552 : Nat := 451709616401150986954331

theorem tailTrace_1319552 : CollatzResearch.WordTrace tailWord_1319552 prefixEnd_1319552 451709616401150986954331 := by
  unfold tailWord_1319552
  simp only [CollatzResearch.WordTrace]
  refine ⟨24064007657747970192380455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32085343543663960256507273 24064007657747970192380455)
  ·
    refine ⟨36096011486621955288570683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24064007657747970192380455 36096011486621955288570683)
    ·
      refine ⟨54144017229932932932856025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36096011486621955288570683 54144017229932932932856025)
      ·
        refine ⟨40608012922449699699642019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54144017229932932932856025 40608012922449699699642019)
        ·
          refine ⟨60912019383674549549463029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40608012922449699699642019 60912019383674549549463029)
          ·
            refine ⟨5710501817219489020262159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60912019383674549549463029 5710501817219489020262159)
            ·
              refine ⟨8565752725829233530393239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5710501817219489020262159 8565752725829233530393239)
              ·
                refine ⟨12848629088743850295589859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8565752725829233530393239 12848629088743850295589859)
                ·
                  refine ⟨19272943633115775443384789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12848629088743850295589859 19272943633115775443384789)
                  ·
                    refine ⟨451709616401150986954331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19272943633115775443384789 451709616401150986954331)
                    ·
                      rfl

theorem cell22_1319552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_1319552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319552 prefixEnd_1319552 := by exact prefixLift 1319552
  have htrace : WordTrace (prefixWord ++ tailWord_1319552) baseStart_1319552 baseEnd_1319552 := by
    simpa [prefixWord, tailWord_1319552, baseEnd_1319552] using wordTrace_append hprefix tailTrace_1319552
  have hstable : (prefixWord ++ tailWord_1319552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319552).length < 2 ^ (prefixWord ++ tailWord_1319552).sum := by decide
  have hdescent : baseEnd_1319552 < baseStart_1319552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319599 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 6]
def baseStart_1319599 : Nat := 118140960795 + 1319599 * 2 ^ 59
def prefixEnd_1319599 : Nat := 4983230072969 + 3 ^ 40 * 1319599 * 2
def baseEnd_1319599 : Nat := 150575235153886177009729

theorem tailTrace_1319599 : CollatzResearch.WordTrace tailWord_1319599 prefixEnd_1319599 150575235153886177009729 := by
  unfold tailWord_1319599
  simp only [CollatzResearch.WordTrace]
  refine ⟨48129729546325667411721851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32086486364217111607814567 48129729546325667411721851)
  ·
    refine ⟨72194594319488501117582777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48129729546325667411721851 72194594319488501117582777)
    ·
      refine ⟨54145945739616375838187083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72194594319488501117582777 54145945739616375838187083)
      ·
        refine ⟨81218918609424563757280625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54145945739616375838187083 81218918609424563757280625)
        ·
          refine ⟨60914188957068422817960469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81218918609424563757280625 60914188957068422817960469)
          ·
            refine ⟨2855352607362582319591897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60914188957068422817960469 2855352607362582319591897)
            ·
              refine ⟨2141514455521936739693923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2855352607362582319591897 2141514455521936739693923)
              ·
                refine ⟨3212271683282905109540885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141514455521936739693923 3212271683282905109540885)
                ·
                  refine ⟨150575235153886177009729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3212271683282905109540885 150575235153886177009729)
                  ·
                    rfl

theorem cell22_1319599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 6].length) (baseStart_1319599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319599 prefixEnd_1319599 := by exact prefixLift 1319599
  have htrace : WordTrace (prefixWord ++ tailWord_1319599) baseStart_1319599 baseEnd_1319599 := by
    simpa [prefixWord, tailWord_1319599, baseEnd_1319599] using wordTrace_append hprefix tailTrace_1319599
  have hstable : (prefixWord ++ tailWord_1319599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319599).length < 2 ^ (prefixWord ++ tailWord_1319599).sum := by decide
  have hdescent : baseEnd_1319599 < baseStart_1319599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319669 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1319669 : Nat := 118140960795 + 1319669 * 2 ^ 59
def prefixEnd_1319669 : Nat := 4983230072969 + 3 ^ 40 * 1319669 * 2
def baseEnd_1319669 : Nat := 451749667892201681778973

theorem tailTrace_1319669 : CollatzResearch.WordTrace tailWord_1319669 prefixEnd_1319669 451749667892201681778973 := by
  unfold tailWord_1319669
  simp only [CollatzResearch.WordTrace]
  refine ⟨48132282656072069366770061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32088188437381379577846707 48132282656072069366770061)
  ·
    refine ⟨18049605996027026012538773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48132282656072069366770061 18049605996027026012538773)
    ·
      refine ⟨846075281063766844337755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18049605996027026012538773 846075281063766844337755)
      ·
        refine ⟨1269112921595650266506633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846075281063766844337755 1269112921595650266506633)
        ·
          refine ⟨951834691196737699879975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1269112921595650266506633 951834691196737699879975)
          ·
            refine ⟨1427752036795106549819963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951834691196737699879975 1427752036795106549819963)
            ·
              refine ⟨2141628055192659824729945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427752036795106549819963 2141628055192659824729945)
              ·
                refine ⟨1606221041394494868547459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141628055192659824729945 1606221041394494868547459)
                ·
                  refine ⟨2409331562091742302821189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606221041394494868547459 2409331562091742302821189)
                  ·
                    refine ⟨451749667892201681778973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2409331562091742302821189 451749667892201681778973)
                    ·
                      rfl

theorem cell22_1319669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1319669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319669 prefixEnd_1319669 := by exact prefixLift 1319669
  have htrace : WordTrace (prefixWord ++ tailWord_1319669) baseStart_1319669 baseEnd_1319669 := by
    simpa [prefixWord, tailWord_1319669, baseEnd_1319669] using wordTrace_append hprefix tailTrace_1319669
  have hstable : (prefixWord ++ tailWord_1319669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319669).length < 2 ^ (prefixWord ++ tailWord_1319669).sum := by decide
  have hdescent : baseEnd_1319669 < baseStart_1319669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319704 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_1319704 : Nat := 118140960795 + 1319704 * 2 ^ 59
def prefixEnd_1319704 : Nat := 4983230072969 + 3 ^ 40 * 1319704 * 2
def baseEnd_1319704 : Nat := 451761649107473257153865

theorem tailTrace_1319704 : CollatzResearch.WordTrace tailWord_1319704 prefixEnd_1319704 451761649107473257153865 := by
  unfold tailWord_1319704
  simp only [CollatzResearch.WordTrace]
  refine ⟨24066779605472635172147083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32089039473963513562862777 24066779605472635172147083)
  ·
    refine ⟨36100169408208952758220625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24066779605472635172147083 36100169408208952758220625)
    ·
      refine ⟨27075127056156714568665469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36100169408208952758220625 27075127056156714568665469)
      ·
        refine ⟨10153172646058767963249551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27075127056156714568665469 10153172646058767963249551)
        ·
          refine ⟨15229758969088151944874327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10153172646058767963249551 15229758969088151944874327)
          ·
            refine ⟨22844638453632227917311491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15229758969088151944874327 22844638453632227917311491)
            ·
              refine ⟨34266957680448341875967237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22844638453632227917311491 34266957680448341875967237)
              ·
                refine ⟨6425054565084064101743857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34266957680448341875967237 6425054565084064101743857)
                ·
                  refine ⟨4818790923813048076307893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6425054565084064101743857 4818790923813048076307893)
                  ·
                    refine ⟨451761649107473257153865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4818790923813048076307893 451761649107473257153865)
                    ·
                      rfl

theorem cell22_1319704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_1319704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319704 prefixEnd_1319704 := by exact prefixLift 1319704
  have htrace : WordTrace (prefixWord ++ tailWord_1319704) baseStart_1319704 baseEnd_1319704 := by
    simpa [prefixWord, tailWord_1319704, baseEnd_1319704] using wordTrace_append hprefix tailTrace_1319704
  have hstable : (prefixWord ++ tailWord_1319704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319704).length < 2 ^ (prefixWord ++ tailWord_1319704).sum := by decide
  have hdescent : baseEnd_1319704 < baseStart_1319704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319706 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_1319706 : Nat := 118140960795 + 1319706 * 2 ^ 59
def prefixEnd_1319706 : Nat := 4983230072969 + 3 ^ 40 * 1319706 * 2
def baseEnd_1319706 : Nat := 150587444582781972867953

theorem tailTrace_1319706 : CollatzResearch.WordTrace tailWord_1319706 prefixEnd_1319706 150587444582781972867953 := by
  unfold tailWord_1319706
  simp only [CollatzResearch.WordTrace]
  refine ⟨12033408039234506171466743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32089088104625349790577981 12033408039234506171466743)
  ·
    refine ⟨18050112058851759257200115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12033408039234506171466743 18050112058851759257200115)
    ·
      refine ⟨27075168088277638885800173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18050112058851759257200115 27075168088277638885800173)
      ·
        refine ⟨10153188033104114582175065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27075168088277638885800173 10153188033104114582175065)
        ·
          refine ⟨7614891024828085936631299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10153188033104114582175065 7614891024828085936631299)
          ·
            refine ⟨11422336537242128904946949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7614891024828085936631299 11422336537242128904946949)
            ·
              refine ⟨2141688100732899169677553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11422336537242128904946949 2141688100732899169677553)
              ·
                refine ⟨1606266075549674377258165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141688100732899169677553 1606266075549674377258165)
                ·
                  refine ⟨150587444582781972867953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1606266075549674377258165 150587444582781972867953)
                  ·
                    rfl

theorem cell22_1319706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_1319706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319706 prefixEnd_1319706 := by exact prefixLift 1319706
  have htrace : WordTrace (prefixWord ++ tailWord_1319706) baseStart_1319706 baseEnd_1319706 := by
    simpa [prefixWord, tailWord_1319706, baseEnd_1319706] using wordTrace_append hprefix tailTrace_1319706
  have hstable : (prefixWord ++ tailWord_1319706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319706).length < 2 ^ (prefixWord ++ tailWord_1319706).sum := by decide
  have hdescent : baseEnd_1319706 < baseStart_1319706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319736 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_1319736 : Nat := 118140960795 + 1319736 * 2 ^ 59
def prefixEnd_1319736 : Nat := 4983230072969 + 3 ^ 40 * 1319736 * 2
def baseEnd_1319736 : Nat := 451772603361435840353767

theorem tailTrace_1319736 : CollatzResearch.WordTrace tailWord_1319736 prefixEnd_1319736 451772603361435840353767 := by
  unfold tailWord_1319736
  simp only [CollatzResearch.WordTrace]
  refine ⟨24067363173414669904729531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32089817564552893206306041 24067363173414669904729531)
  ·
    refine ⟨36101044760122004857094297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24067363173414669904729531 36101044760122004857094297)
    ·
      refine ⟨27075783570091503642820723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36101044760122004857094297 27075783570091503642820723)
      ·
        refine ⟨40613675355137255464231085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27075783570091503642820723 40613675355137255464231085)
        ·
          refine ⟨15230128258176470799086657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40613675355137255464231085 15230128258176470799086657)
          ·
            refine ⟨11422596193632353099314993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15230128258176470799086657 11422596193632353099314993)
            ·
              refine ⟨8566947145224264824486245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11422596193632353099314993 8566947145224264824486245)
              ·
                refine ⟨1606302589729549654591171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8566947145224264824486245 1606302589729549654591171)
                ·
                  refine ⟨2409453884594324481886757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606302589729549654591171 2409453884594324481886757)
                  ·
                    refine ⟨451772603361435840353767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2409453884594324481886757 451772603361435840353767)
                    ·
                      rfl

theorem cell22_1319736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_1319736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319736 prefixEnd_1319736 := by exact prefixLift 1319736
  have htrace : WordTrace (prefixWord ++ tailWord_1319736) baseStart_1319736 baseEnd_1319736 := by
    simpa [prefixWord, tailWord_1319736, baseEnd_1319736] using wordTrace_append hprefix tailTrace_1319736
  have hstable : (prefixWord ++ tailWord_1319736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319736).length < 2 ^ (prefixWord ++ tailWord_1319736).sum := by decide
  have hdescent : baseEnd_1319736 < baseStart_1319736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319749 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_1319749 : Nat := 118140960795 + 1319749 * 2 ^ 59
def prefixEnd_1319749 : Nat := 4983230072969 + 3 ^ 40 * 1319749 * 2
def baseEnd_1319749 : Nat := 451777053527108139778727

theorem tailTrace_1319749 : CollatzResearch.WordTrace tailWord_1319749 prefixEnd_1319749 451777053527108139778727 := by
  unfold tailWord_1319749
  simp only [CollatzResearch.WordTrace]
  refine ⟨48135200495782243029682301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32090133663854828686454867 48135200495782243029682301)
  ·
    refine ⟨18050700185918341136130863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48135200495782243029682301 18050700185918341136130863)
    ·
      refine ⟨27076050278877511704196295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18050700185918341136130863 27076050278877511704196295)
      ·
        refine ⟨40614075418316267556294443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27076050278877511704196295 40614075418316267556294443)
        ·
          refine ⟨60921113127474401334441665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40614075418316267556294443 60921113127474401334441665)
          ·
            refine ⟨45690834845605801000831249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60921113127474401334441665 45690834845605801000831249)
            ·
              refine ⟨34268126134204350750623437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45690834845605801000831249 34268126134204350750623437)
              ·
                refine ⟨12850547300326631531483789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34268126134204350750623437 12850547300326631531483789)
                ·
                  refine ⟨4818955237622486824306421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12850547300326631531483789 4818955237622486824306421)
                  ·
                    refine ⟨451777053527108139778727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4818955237622486824306421 451777053527108139778727)
                    ·
                      rfl

theorem cell22_1319749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_1319749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319749 prefixEnd_1319749 := by exact prefixLift 1319749
  have htrace : WordTrace (prefixWord ++ tailWord_1319749) baseStart_1319749 baseEnd_1319749 := by
    simpa [prefixWord, tailWord_1319749, baseEnd_1319749] using wordTrace_append hprefix tailTrace_1319749
  have hstable : (prefixWord ++ tailWord_1319749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319749).length < 2 ^ (prefixWord ++ tailWord_1319749).sum := by decide
  have hdescent : baseEnd_1319749 < baseStart_1319749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319753 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 1, 4]
def baseStart_1319753 : Nat := 118140960795 + 1319753 * 2 ^ 59
def prefixEnd_1319753 : Nat := 4983230072969 + 3 ^ 40 * 1319753 * 2
def baseEnd_1319753 : Nat := 451778422808853462678715

theorem tailTrace_1319753 : CollatzResearch.WordTrace tailWord_1319753 prefixEnd_1319753 451778422808853462678715 := by
  unfold tailWord_1319753
  simp only [CollatzResearch.WordTrace]
  refine ⟨48135346387767751712827913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32090230925178501141885275 48135346387767751712827913)
  ·
    refine ⟨36101509790825813784620935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48135346387767751712827913 36101509790825813784620935)
    ·
      refine ⟨54152264686238720676931403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36101509790825813784620935 54152264686238720676931403)
      ·
        refine ⟨81228397029358081015397105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54152264686238720676931403 81228397029358081015397105)
        ·
          refine ⟨60921297772018560761547829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81228397029358081015397105 60921297772018560761547829)
          ·
            refine ⟨5711371666126740071395109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60921297772018560761547829 5711371666126740071395109)
            ·
              refine ⟨1070882187398763763386583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5711371666126740071395109 1070882187398763763386583)
              ·
                refine ⟨1606323281098145645079875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070882187398763763386583 1606323281098145645079875)
                ·
                  refine ⟨2409484921647218467619813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606323281098145645079875 2409484921647218467619813)
                  ·
                    refine ⟨451778422808853462678715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2409484921647218467619813 451778422808853462678715)
                    ·
                      rfl

theorem cell22_1319753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_1319753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319753 prefixEnd_1319753 := by exact prefixLift 1319753
  have htrace : WordTrace (prefixWord ++ tailWord_1319753) baseStart_1319753 baseEnd_1319753 := by
    simpa [prefixWord, tailWord_1319753, baseEnd_1319753] using wordTrace_append hprefix tailTrace_1319753
  have hstable : (prefixWord ++ tailWord_1319753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319753).length < 2 ^ (prefixWord ++ tailWord_1319753).sum := by decide
  have hdescent : baseEnd_1319753 < baseStart_1319753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319757 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1319757 : Nat := 118140960795 + 1319757 * 2 ^ 59
def prefixEnd_1319757 : Nat := 4983230072969 + 3 ^ 40 * 1319757 * 2
def baseEnd_1319757 : Nat := 150593264030199595192901

theorem tailTrace_1319757 : CollatzResearch.WordTrace tailWord_1319757 prefixEnd_1319757 150593264030199595192901 := by
  unfold tailWord_1319757
  simp only [CollatzResearch.WordTrace]
  refine ⟨48135492279753260395973525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32090328186502173597315683 48135492279753260395973525)
  ·
    refine ⟨2256351200613434081061259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48135492279753260395973525 2256351200613434081061259)
    ·
      refine ⟨3384526800920151121591889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256351200613434081061259 3384526800920151121591889)
      ·
        refine ⟨2538395100690113341193917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3384526800920151121591889 2538395100690113341193917)
        ·
          refine ⟨951898162758792502947719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2538395100690113341193917 951898162758792502947719)
          ·
            refine ⟨1427847244138188754421579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951898162758792502947719 1427847244138188754421579)
            ·
              refine ⟨2141770866207283131632369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427847244138188754421579 2141770866207283131632369)
              ·
                refine ⟨1606328149655462348724277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141770866207283131632369 1606328149655462348724277)
                ·
                  refine ⟨150593264030199595192901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1606328149655462348724277 150593264030199595192901)
                  ·
                    rfl

theorem cell22_1319757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1319757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319757 prefixEnd_1319757 := by exact prefixLift 1319757
  have htrace : WordTrace (prefixWord ++ tailWord_1319757) baseStart_1319757 baseEnd_1319757 := by
    simpa [prefixWord, tailWord_1319757, baseEnd_1319757] using wordTrace_append hprefix tailTrace_1319757
  have hstable : (prefixWord ++ tailWord_1319757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319757).length < 2 ^ (prefixWord ++ tailWord_1319757).sum := by decide
  have hdescent : baseEnd_1319757 < baseStart_1319757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319783 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1319783 : Nat := 118140960795 + 1319783 * 2 ^ 59
def prefixEnd_1319783 : Nat := 4983230072969 + 3 ^ 40 * 1319783 * 2
def baseEnd_1319783 : Nat := 451788692421943384428623

theorem tailTrace_1319783 : CollatzResearch.WordTrace tailWord_1319783 prefixEnd_1319783 451788692421943384428623 := by
  unfold tailWord_1319783
  simp only [CollatzResearch.WordTrace]
  refine ⟨48136440577659066836420003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32090960385106044557613335 48136440577659066836420003)
  ·
    refine ⟨72204660866488600254630005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48136440577659066836420003 72204660866488600254630005)
    ·
      refine ⟨6769186956233306273871563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72204660866488600254630005 6769186956233306273871563)
      ·
        refine ⟨10153780434349959410807345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6769186956233306273871563 10153780434349959410807345)
        ·
          refine ⟨7615335325762469558105509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10153780434349959410807345 7615335325762469558105509)
          ·
            refine ⟨1427875373580463042144783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7615335325762469558105509 1427875373580463042144783)
            ·
              refine ⟨2141813060370694563217175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427875373580463042144783 2141813060370694563217175)
              ·
                refine ⟨3212719590556041844825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141813060370694563217175 3212719590556041844825763)
                ·
                  refine ⟨4819079385834062767238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212719590556041844825763 4819079385834062767238645)
                  ·
                    refine ⟨451788692421943384428623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4819079385834062767238645 451788692421943384428623)
                    ·
                      rfl

theorem cell22_1319783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1319783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319783 prefixEnd_1319783 := by exact prefixLift 1319783
  have htrace : WordTrace (prefixWord ++ tailWord_1319783) baseStart_1319783 baseEnd_1319783 := by
    simpa [prefixWord, tailWord_1319783, baseEnd_1319783] using wordTrace_append hprefix tailTrace_1319783
  have hstable : (prefixWord ++ tailWord_1319783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319783).length < 2 ^ (prefixWord ++ tailWord_1319783).sum := by decide
  have hdescent : baseEnd_1319783 < baseStart_1319783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319798 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_1319798 : Nat := 118140960795 + 1319798 * 2 ^ 59
def prefixEnd_1319798 : Nat := 4983230072969 + 3 ^ 40 * 1319798 * 2
def baseEnd_1319798 : Nat := 451793827228488345303577

theorem tailTrace_1319798 : CollatzResearch.WordTrace tailWord_1319798 prefixEnd_1319798 451793827228488345303577 := by
  unfold tailWord_1319798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008561729537795274888503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32091325115069816265477365 3008561729537795274888503)
  ·
    refine ⟨4512842594306692912332755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3008561729537795274888503 4512842594306692912332755)
    ·
      refine ⟨6769263891460039368499133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4512842594306692912332755 6769263891460039368499133)
      ·
        refine ⟨2538473959297514763187175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6769263891460039368499133 2538473959297514763187175)
        ·
          refine ⟨3807710938946272144780763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538473959297514763187175 3807710938946272144780763)
          ·
            refine ⟨5711566408419408217171145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807710938946272144780763 5711566408419408217171145)
            ·
              refine ⟨4283674806314556162878359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5711566408419408217171145 4283674806314556162878359)
              ·
                refine ⟨6425512209471834244317539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283674806314556162878359 6425512209471834244317539)
                ·
                  refine ⟨9638268314207751366476309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425512209471834244317539 9638268314207751366476309)
                  ·
                    refine ⟨451793827228488345303577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9638268314207751366476309 451793827228488345303577)
                    ·
                      rfl

theorem cell22_1319798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_1319798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319798 prefixEnd_1319798 := by exact prefixLift 1319798
  have htrace : WordTrace (prefixWord ++ tailWord_1319798) baseStart_1319798 baseEnd_1319798 := by
    simpa [prefixWord, tailWord_1319798, baseEnd_1319798] using wordTrace_append hprefix tailTrace_1319798
  have hstable : (prefixWord ++ tailWord_1319798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319798).length < 2 ^ (prefixWord ++ tailWord_1319798).sum := by decide
  have hdescent : baseEnd_1319798 < baseStart_1319798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319824 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 11]
def baseStart_1319824 : Nat := 118140960795 + 1319824 * 2 ^ 59
def prefixEnd_1319824 : Nat := 4983230072969 + 3 ^ 40 * 1319824 * 2
def baseEnd_1319824 : Nat := 150600909186610981384499

theorem tailTrace_1319824 : CollatzResearch.WordTrace tailWord_1319824 prefixEnd_1319824 150600909186610981384499 := by
  unfold tailWord_1319824
  simp only [CollatzResearch.WordTrace]
  refine ⟨24068967985255265419331263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32091957313673687225775017 24068967985255265419331263)
  ·
    refine ⟨36103451977882898128996895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24068967985255265419331263 36103451977882898128996895)
    ·
      refine ⟨54155177966824347193495343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36103451977882898128996895 54155177966824347193495343)
      ·
        refine ⟨81232766950236520790243015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54155177966824347193495343 81232766950236520790243015)
        ·
          refine ⟨121849150425354781185364523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81232766950236520790243015 121849150425354781185364523)
          ·
            refine ⟨182773725638032171778046785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121849150425354781185364523 182773725638032171778046785)
            ·
              refine ⟨137080294228524128833535089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182773725638032171778046785 137080294228524128833535089)
              ·
                refine ⟨102810220671393096625151317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137080294228524128833535089 102810220671393096625151317)
                ·
                  refine ⟨150600909186610981384499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 102810220671393096625151317 150600909186610981384499)
                  ·
                    rfl

theorem cell22_1319824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_1319824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319824 prefixEnd_1319824 := by exact prefixLift 1319824
  have htrace : WordTrace (prefixWord ++ tailWord_1319824) baseStart_1319824 baseEnd_1319824 := by
    simpa [prefixWord, tailWord_1319824, baseEnd_1319824] using wordTrace_append hprefix tailTrace_1319824
  have hstable : (prefixWord ++ tailWord_1319824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319824).length < 2 ^ (prefixWord ++ tailWord_1319824).sum := by decide
  have hdescent : baseEnd_1319824 < baseStart_1319824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319830 : List Nat := [5, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1319830 : Nat := 118140960795 + 1319830 * 2 ^ 59
def prefixEnd_1319830 : Nat := 4983230072969 + 3 ^ 40 * 1319830 * 2
def baseEnd_1319830 : Nat := 50200531275827880944831

theorem tailTrace_1319830 : CollatzResearch.WordTrace tailWord_1319830 prefixEnd_1319830 50200531275827880944831 := by
  unfold tailWord_1319830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008634675530549616461309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32092103205659195908920629 3008634675530549616461309)
  ·
    refine ⟨1128238003323956106172991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3008634675530549616461309 1128238003323956106172991)
    ·
      refine ⟨1692357004985934159259487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128238003323956106172991 1692357004985934159259487)
      ·
        refine ⟨2538535507478901238889231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692357004985934159259487 2538535507478901238889231)
        ·
          refine ⟨3807803261218351858333847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538535507478901238889231 3807803261218351858333847)
          ·
            refine ⟨5711704891827527787500771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807803261218351858333847 5711704891827527787500771)
            ·
              refine ⟨8567557337741291681251157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711704891827527787500771 8567557337741291681251157)
              ·
                refine ⟨50200531275827880944831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8567557337741291681251157 50200531275827880944831)
                ·
                  rfl

theorem cell22_1319830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1319830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319830 prefixEnd_1319830 := by exact prefixLift 1319830
  have htrace : WordTrace (prefixWord ++ tailWord_1319830) baseStart_1319830 baseEnd_1319830 := by
    simpa [prefixWord, tailWord_1319830, baseEnd_1319830] using wordTrace_append hprefix tailTrace_1319830
  have hstable : (prefixWord ++ tailWord_1319830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319830).length < 2 ^ (prefixWord ++ tailWord_1319830).sum := by decide
  have hdescent : baseEnd_1319830 < baseStart_1319830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319834 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_1319834 : Nat := 118140960795 + 1319834 * 2 ^ 59
def prefixEnd_1319834 : Nat := 4983230072969 + 3 ^ 40 * 1319834 * 2
def baseEnd_1319834 : Nat := 451806150764196251403467

theorem tailTrace_1319834 : CollatzResearch.WordTrace tailWord_1319834 prefixEnd_1319834 451806150764196251403467 := by
  unfold tailWord_1319834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12034575175118575636631639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32092200466982868364351037 12034575175118575636631639)
  ·
    refine ⟨18051862762677863454947459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12034575175118575636631639 18051862762677863454947459)
    ·
      refine ⟨27077794144016795182421189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18051862762677863454947459 27077794144016795182421189)
      ·
        refine ⟨5077086402003149096703973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27077794144016795182421189 5077086402003149096703973)
        ·
          refine ⟨951953700375590455631995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5077086402003149096703973 951953700375590455631995)
          ·
            refine ⟨1427930550563385683447993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951953700375590455631995 1427930550563385683447993)
            ·
              refine ⟨1070947912922539262585995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1427930550563385683447993 1070947912922539262585995)
              ·
                refine ⟨1606421869383808893878993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070947912922539262585995 1606421869383808893878993)
                ·
                  refine ⟨1204816402037856670409245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1606421869383808893878993 1204816402037856670409245)
                  ·
                    refine ⟨451806150764196251403467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204816402037856670409245 451806150764196251403467)
                    ·
                      rfl

theorem cell22_1319834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_1319834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319834 prefixEnd_1319834 := by exact prefixLift 1319834
  have htrace : WordTrace (prefixWord ++ tailWord_1319834) baseStart_1319834 baseEnd_1319834 := by
    simpa [prefixWord, tailWord_1319834, baseEnd_1319834] using wordTrace_append hprefix tailTrace_1319834
  have hstable : (prefixWord ++ tailWord_1319834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319834).length < 2 ^ (prefixWord ++ tailWord_1319834).sum := by decide
  have hdescent : baseEnd_1319834 < baseStart_1319834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319903 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 6]
def baseStart_1319903 : Nat := 118140960795 + 1319903 * 2 ^ 59
def prefixEnd_1319903 : Nat := 4983230072969 + 3 ^ 40 * 1319903 * 2
def baseEnd_1319903 : Nat := 150609923624767690476085

theorem tailTrace_1319903 : CollatzResearch.WordTrace tailWord_1319903 prefixEnd_1319903 150609923624767690476085 := by
  unfold tailWord_1319903
  simp only [CollatzResearch.WordTrace]
  refine ⟨48140817337224327330788363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32093878224816218220525575 48140817337224327330788363)
  ·
    refine ⟨72211226005836490996182545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48140817337224327330788363 72211226005836490996182545)
    ·
      refine ⟨54158419504377368247136909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72211226005836490996182545 54158419504377368247136909)
      ·
        refine ⟨20309407314141513092676341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54158419504377368247136909 20309407314141513092676341)
        ·
          refine ⟨1904006935700766852438407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20309407314141513092676341 1904006935700766852438407)
          ·
            refine ⟨2856010403551150278657611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904006935700766852438407 2856010403551150278657611)
            ·
              refine ⟨4284015605326725417986417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856010403551150278657611 4284015605326725417986417)
              ·
                refine ⟨3213011703995044063489813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4284015605326725417986417 3213011703995044063489813)
                ·
                  refine ⟨150609923624767690476085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3213011703995044063489813 150609923624767690476085)
                  ·
                    rfl

theorem cell22_1319903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 6].length) (baseStart_1319903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319903 prefixEnd_1319903 := by exact prefixLift 1319903
  have htrace : WordTrace (prefixWord ++ tailWord_1319903) baseStart_1319903 baseEnd_1319903 := by
    simpa [prefixWord, tailWord_1319903, baseEnd_1319903] using wordTrace_append hprefix tailTrace_1319903
  have hstable : (prefixWord ++ tailWord_1319903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319903).length < 2 ^ (prefixWord ++ tailWord_1319903).sum := by decide
  have hdescent : baseEnd_1319903 < baseStart_1319903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319922 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_1319922 : Nat := 118140960795 + 1319922 * 2 ^ 59
def prefixEnd_1319922 : Nat := 4983230072969 + 3 ^ 40 * 1319922 * 2
def baseEnd_1319922 : Nat := 451836274962593355203197

theorem tailTrace_1319922 : CollatzResearch.WordTrace tailWord_1319922 prefixEnd_1319922 451836274962593355203197 := by
  unfold tailWord_1319922
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035377581038873393932505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32094340216103662383820013 12035377581038873393932505)
  ·
    refine ⟨9026533185779155045449379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12035377581038873393932505 9026533185779155045449379)
    ·
      refine ⟨13539799778668732568174069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9026533185779155045449379 13539799778668732568174069)
      ·
        refine ⟨1269356229250193678266319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13539799778668732568174069 1269356229250193678266319)
        ·
          refine ⟨1904034343875290517399479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269356229250193678266319 1904034343875290517399479)
          ·
            refine ⟨2856051515812935776099219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904034343875290517399479 2856051515812935776099219)
            ·
              refine ⟨4284077273719403664148829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856051515812935776099219 4284077273719403664148829)
              ·
                refine ⟨1606528977644776374055811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4284077273719403664148829 1606528977644776374055811)
                ·
                  refine ⟨2409793466467164561083717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606528977644776374055811 2409793466467164561083717)
                  ·
                    refine ⟨451836274962593355203197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2409793466467164561083717 451836274962593355203197)
                    ·
                      rfl

theorem cell22_1319922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_1319922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319922 prefixEnd_1319922 := by exact prefixLift 1319922
  have htrace : WordTrace (prefixWord ++ tailWord_1319922) baseStart_1319922 baseEnd_1319922 := by
    simpa [prefixWord, tailWord_1319922, baseEnd_1319922] using wordTrace_append hprefix tailTrace_1319922
  have hstable : (prefixWord ++ tailWord_1319922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319922).length < 2 ^ (prefixWord ++ tailWord_1319922).sum := by decide
  have hdescent : baseEnd_1319922 < baseStart_1319922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319961 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_1319961 : Nat := 118140960795 + 1319961 * 2 ^ 59
def prefixEnd_1319961 : Nat := 4983230072969 + 3 ^ 40 * 1319961 * 2
def baseEnd_1319961 : Nat := 451849625459610253478077

theorem tailTrace_1319961 : CollatzResearch.WordTrace tailWord_1319961 prefixEnd_1319961 451849625459610253478077 := by
  unfold tailWord_1319961
  simp only [CollatzResearch.WordTrace]
  refine ⟨48142932771014203236399737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32095288514009468824266491 48142932771014203236399737)
  ·
    refine ⟨36107199578260652427299803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48142932771014203236399737 36107199578260652427299803)
    ·
      refine ⟨54160799367390978640949705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36107199578260652427299803 54160799367390978640949705)
      ·
        refine ⟨40620599525543233980712279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54160799367390978640949705 40620599525543233980712279)
        ·
          refine ⟨60930899288314850971068419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40620599525543233980712279 60930899288314850971068419)
          ·
            refine ⟨91396348932472276456602629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60930899288314850971068419 91396348932472276456602629)
            ·
              refine ⟨17136815424838551835612993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91396348932472276456602629 17136815424838551835612993)
              ·
                refine ⟨12852611568628913876709745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17136815424838551835612993 12852611568628913876709745)
                ·
                  refine ⟨9639458676471685407532309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12852611568628913876709745 9639458676471685407532309)
                  ·
                    refine ⟨451849625459610253478077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9639458676471685407532309 451849625459610253478077)
                    ·
                      rfl

theorem cell22_1319961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_1319961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319961 prefixEnd_1319961 := by exact prefixLift 1319961
  have htrace : WordTrace (prefixWord ++ tailWord_1319961) baseStart_1319961 baseEnd_1319961 := by
    simpa [prefixWord, tailWord_1319961, baseEnd_1319961] using wordTrace_append hprefix tailTrace_1319961
  have hstable : (prefixWord ++ tailWord_1319961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319961).length < 2 ^ (prefixWord ++ tailWord_1319961).sum := by decide
  have hdescent : baseEnd_1319961 < baseStart_1319961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319993 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 7]
def baseStart_1319993 : Nat := 118140960795 + 1319993 * 2 ^ 59
def prefixEnd_1319993 : Nat := 4983230072969 + 3 ^ 40 * 1319993 * 2
def baseEnd_1319993 : Nat := 150620193237857612225993

theorem tailTrace_1319993 : CollatzResearch.WordTrace tailWord_1319993 prefixEnd_1319993 150620193237857612225993 := by
  unfold tailWord_1319993
  simp only [CollatzResearch.WordTrace]
  refine ⟨48144099906898272701564633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32096066604598848467709755 48144099906898272701564633)
  ·
    refine ⟨36108074930173704526173475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48144099906898272701564633 36108074930173704526173475)
    ·
      refine ⟨54162112395260556789260213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36108074930173704526173475 54162112395260556789260213)
      ·
        refine ⟨5077698037055677198993145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54162112395260556789260213 5077698037055677198993145)
        ·
          refine ⟨3808273527791757899244859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5077698037055677198993145 3808273527791757899244859)
          ·
            refine ⟨5712410291687636848867289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808273527791757899244859 5712410291687636848867289)
            ·
              refine ⟨4284307718765727636650467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5712410291687636848867289 4284307718765727636650467)
              ·
                refine ⟨6426461578148591454975701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284307718765727636650467 6426461578148591454975701)
                ·
                  refine ⟨150620193237857612225993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6426461578148591454975701 150620193237857612225993)
                  ·
                    rfl

theorem cell22_1319993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_1319993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319993 prefixEnd_1319993 := by exact prefixLift 1319993
  have htrace : WordTrace (prefixWord ++ tailWord_1319993) baseStart_1319993 baseEnd_1319993 := by
    simpa [prefixWord, tailWord_1319993, baseEnd_1319993] using wordTrace_append hprefix tailTrace_1319993
  have hstable : (prefixWord ++ tailWord_1319993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319993).length < 2 ^ (prefixWord ++ tailWord_1319993).sum := by decide
  have hdescent : baseEnd_1319993 < baseStart_1319993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1319997 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1319997 : Nat := 118140960795 + 1319997 * 2 ^ 59
def prefixEnd_1319997 : Nat := 4983230072969 + 3 ^ 40 * 1319997 * 2
def baseEnd_1319997 : Nat := 451861948995318159577967

theorem tailTrace_1319997 : CollatzResearch.WordTrace tailWord_1319997 prefixEnd_1319997 451861948995318159577967 := by
  unfold tailWord_1319997
  simp only [CollatzResearch.WordTrace]
  refine ⟨48144245798883781384710245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32096163865922520923140163 48144245798883781384710245)
  ·
    refine ⟨9027046087290709009633171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48144245798883781384710245 9027046087290709009633171)
    ·
      refine ⟨13540569130936063514449757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9027046087290709009633171 13540569130936063514449757)
      ·
        refine ⟨5077713424101023817918659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13540569130936063514449757 5077713424101023817918659)
        ·
          refine ⟨7616570136151535726877989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077713424101023817918659 7616570136151535726877989)
          ·
            refine ⟨1428106900528412948789623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7616570136151535726877989 1428106900528412948789623)
            ·
              refine ⟨2142160350792619423184435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428106900528412948789623 2142160350792619423184435)
              ·
                refine ⟨3213240526188929134776653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142160350792619423184435 3213240526188929134776653)
                ·
                  refine ⟨1204965197320848425541245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3213240526188929134776653 1204965197320848425541245)
                  ·
                    refine ⟨451861948995318159577967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204965197320848425541245 451861948995318159577967)
                    ·
                      rfl

theorem cell22_1319997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1319997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1319997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1319997 prefixEnd_1319997 := by exact prefixLift 1319997
  have htrace : WordTrace (prefixWord ++ tailWord_1319997) baseStart_1319997 baseEnd_1319997 := by
    simpa [prefixWord, tailWord_1319997, baseEnd_1319997] using wordTrace_append hprefix tailTrace_1319997
  have hstable : (prefixWord ++ tailWord_1319997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1319997).length < 2 ^ (prefixWord ++ tailWord_1319997).sum := by decide
  have hdescent : baseEnd_1319997 < baseStart_1319997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1319997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320010 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_1320010 : Nat := 118140960795 + 1320010 * 2 ^ 59
def prefixEnd_1320010 : Nat := 4983230072969 + 3 ^ 40 * 1320010 * 2
def baseEnd_1320010 : Nat := 150622133053663486334309

theorem tailTrace_1320010 : CollatzResearch.WordTrace tailWord_1320010 prefixEnd_1320010 150622133053663486334309 := by
  unfold tailWord_1320010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12036179986959171151233371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32096479965224456403288989 12036179986959171151233371)
  ·
    refine ⟨18054269980438756726850057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12036179986959171151233371 18054269980438756726850057)
    ·
      refine ⟨13540702485329067545137543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18054269980438756726850057 13540702485329067545137543)
      ·
        refine ⟨20311053727993601317706315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13540702485329067545137543 20311053727993601317706315)
        ·
          refine ⟨30466580591990401976559473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20311053727993601317706315 30466580591990401976559473)
          ·
            refine ⟨22849935443992801482419605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30466580591990401976559473 22849935443992801482419605)
            ·
              refine ⟨1071090723937162569488419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22849935443992801482419605 1071090723937162569488419)
              ·
                refine ⟨1606636085905743854232629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071090723937162569488419 1606636085905743854232629)
                ·
                  refine ⟨150622133053663486334309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1606636085905743854232629 150622133053663486334309)
                  ·
                    rfl

theorem cell22_1320010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_1320010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320010 prefixEnd_1320010 := by exact prefixLift 1320010
  have htrace : WordTrace (prefixWord ++ tailWord_1320010) baseStart_1320010 baseEnd_1320010 := by
    simpa [prefixWord, tailWord_1320010, baseEnd_1320010] using wordTrace_append hprefix tailTrace_1320010
  have hstable : (prefixWord ++ tailWord_1320010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320010).length < 2 ^ (prefixWord ++ tailWord_1320010).sum := by decide
  have hdescent : baseEnd_1320010 < baseStart_1320010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320055 : List Nat := [1, 1, 3, 1, 1, 4, 3, 4, 4]
def baseStart_1320055 : Nat := 118140960795 + 1320055 * 2 ^ 59
def prefixEnd_1320055 : Nat := 4983230072969 + 3 ^ 40 * 1320055 * 2
def baseEnd_1320055 : Nat := 150627267860208447209263

theorem tailTrace_1320055 : CollatzResearch.WordTrace tailWord_1320055 prefixEnd_1320055 150627267860208447209263 := by
  unfold tailWord_1320055
  simp only [CollatzResearch.WordTrace]
  refine ⟨48146361232673657290321619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32097574155115771526881079 48146361232673657290321619)
  ·
    refine ⟨72219541849010485935482429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48146361232673657290321619 72219541849010485935482429)
    ·
      refine ⟨27082328193378932225805911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72219541849010485935482429 27082328193378932225805911)
      ·
        refine ⟨40623492290068398338708867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27082328193378932225805911 40623492290068398338708867)
        ·
          refine ⟨60935238435102597508063301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40623492290068398338708867 60935238435102597508063301)
          ·
            refine ⟨11425357206581737032761869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60935238435102597508063301 11425357206581737032761869)
            ·
              refine ⟨4284508952468151387285701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11425357206581737032761869 4284508952468151387285701)
              ·
                refine ⟨803345428587778385116069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4284508952468151387285701 803345428587778385116069)
                ·
                  refine ⟨150627267860208447209263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803345428587778385116069 150627267860208447209263)
                  ·
                    rfl

theorem cell22_1320055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 4].length) (baseStart_1320055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320055 prefixEnd_1320055 := by exact prefixLift 1320055
  have htrace : WordTrace (prefixWord ++ tailWord_1320055) baseStart_1320055 baseEnd_1320055 := by
    simpa [prefixWord, tailWord_1320055, baseEnd_1320055] using wordTrace_append hprefix tailTrace_1320055
  have hstable : (prefixWord ++ tailWord_1320055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320055).length < 2 ^ (prefixWord ++ tailWord_1320055).sum := by decide
  have hdescent : baseEnd_1320055 < baseStart_1320055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320115 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 3, 3]
def baseStart_1320115 : Nat := 118140960795 + 1320115 * 2 ^ 59
def prefixEnd_1320115 : Nat := 4983230072969 + 3 ^ 40 * 1320115 * 2
def baseEnd_1320115 : Nat := 451902342806805185127605

theorem tailTrace_1320115 : CollatzResearch.WordTrace tailWord_1320115 prefixEnd_1320115 451902342806805185127605 := by
  unfold tailWord_1320115
  simp only [CollatzResearch.WordTrace]
  refine ⟨48148549612456287537505799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32099033074970858358337199 48148549612456287537505799)
  ·
    refine ⟨72222824418684431306258699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48148549612456287537505799 72222824418684431306258699)
    ·
      refine ⟨108334236628026646959388049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72222824418684431306258699 108334236628026646959388049)
      ·
        refine ⟨81250677471019985219541037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108334236628026646959388049 81250677471019985219541037)
        ·
          refine ⟨30469004051632494457327889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81250677471019985219541037 30469004051632494457327889)
          ·
            refine ⟨22851753038724370842995917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30469004051632494457327889 22851753038724370842995917)
            ·
              refine ⟨8569407389521639066123469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22851753038724370842995917 8569407389521639066123469)
              ·
                refine ⟨3213527771070614649796301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8569407389521639066123469 3213527771070614649796301)
                ·
                  refine ⟨1205072914151480493673613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3213527771070614649796301 1205072914151480493673613)
                  ·
                    refine ⟨451902342806805185127605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205072914151480493673613 451902342806805185127605)
                    ·
                      rfl

theorem cell22_1320115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 3].length) (baseStart_1320115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320115 prefixEnd_1320115 := by exact prefixLift 1320115
  have htrace : WordTrace (prefixWord ++ tailWord_1320115) baseStart_1320115 baseEnd_1320115 := by
    simpa [prefixWord, tailWord_1320115, baseEnd_1320115] using wordTrace_append hprefix tailTrace_1320115
  have hstable : (prefixWord ++ tailWord_1320115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320115).length < 2 ^ (prefixWord ++ tailWord_1320115).sum := by decide
  have hdescent : baseEnd_1320115 < baseStart_1320115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320143 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 4, 5]
def baseStart_1320143 : Nat := 118140960795 + 1320143 * 2 ^ 59
def prefixEnd_1320143 : Nat := 4983230072969 + 3 ^ 40 * 1320143 * 2
def baseEnd_1320143 : Nat := 451911927779022445427519

theorem tailTrace_1320143 : CollatzResearch.WordTrace tailWord_1320143 prefixEnd_1320143 451911927779022445427519 := by
  unfold tailWord_1320143
  simp only [CollatzResearch.WordTrace]
  refine ⟨48149570856354848319525083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32099713904236565546350055 48149570856354848319525083)
  ·
    refine ⟨72224356284532272479287625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48149570856354848319525083 72224356284532272479287625)
    ·
      refine ⟨54168267213399204359465719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72224356284532272479287625 54168267213399204359465719)
      ·
        refine ⟨81252400820098806539198579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54168267213399204359465719 81252400820098806539198579)
        ·
          refine ⟨121878601230148209808797869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81252400820098806539198579 121878601230148209808797869)
          ·
            refine ⟨45704475461305578678299201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121878601230148209808797869 45704475461305578678299201)
            ·
              refine ⟨34278356595979184008724401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45704475461305578678299201 34278356595979184008724401)
              ·
                refine ⟨25708767446984388006543301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34278356595979184008724401 25708767446984388006543301)
                ·
                  refine ⟨4820393896309572751226869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25708767446984388006543301 4820393896309572751226869)
                  ·
                    refine ⟨451911927779022445427519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4820393896309572751226869 451911927779022445427519)
                    ·
                      rfl

theorem cell22_1320143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_1320143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320143 prefixEnd_1320143 := by exact prefixLift 1320143
  have htrace : WordTrace (prefixWord ++ tailWord_1320143) baseStart_1320143 baseEnd_1320143 := by
    simpa [prefixWord, tailWord_1320143, baseEnd_1320143] using wordTrace_append hprefix tailTrace_1320143
  have hstable : (prefixWord ++ tailWord_1320143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320143).length < 2 ^ (prefixWord ++ tailWord_1320143).sum := by decide
  have hdescent : baseEnd_1320143 < baseStart_1320143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320224 : List Nat := [2, 1, 1, 5, 3, 1, 1, 4, 4]
def baseStart_1320224 : Nat := 118140960795 + 1320224 * 2 ^ 59
def prefixEnd_1320224 : Nat := 4983230072969 + 3 ^ 40 * 1320224 * 2
def baseEnd_1320224 : Nat := 150646551911455078050757

theorem tailTrace_1320224 : CollatzResearch.WordTrace tailWord_1320224 prefixEnd_1320224 150646551911455078050757 := by
  unfold tailWord_1320224
  simp only [CollatzResearch.WordTrace]
  refine ⟨24076262584530699576611863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32101683446040932768815817 24076262584530699576611863)
  ·
    refine ⟨36114393876796049364917795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24076262584530699576611863 36114393876796049364917795)
    ·
      refine ⟨54171590815194074047376693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36114393876796049364917795 54171590815194074047376693)
      ·
        refine ⟨5078586638924444441941565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54171590815194074047376693 5078586638924444441941565)
        ·
          refine ⟨1904469989596666665728087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5078586638924444441941565 1904469989596666665728087)
          ·
            refine ⟨2856704984394999998592131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904469989596666665728087 2856704984394999998592131)
            ·
              refine ⟨4285057476592499997888197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856704984394999998592131 4285057476592499997888197)
              ·
                refine ⟨803448276861093749604037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4285057476592499997888197 803448276861093749604037)
                ·
                  refine ⟨150646551911455078050757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803448276861093749604037 150646551911455078050757)
                  ·
                    rfl

theorem cell22_1320224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_1320224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320224 prefixEnd_1320224 := by exact prefixLift 1320224
  have htrace : WordTrace (prefixWord ++ tailWord_1320224) baseStart_1320224 baseEnd_1320224 := by
    simpa [prefixWord, tailWord_1320224, baseEnd_1320224] using wordTrace_append hprefix tailTrace_1320224
  have hstable : (prefixWord ++ tailWord_1320224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320224).length < 2 ^ (prefixWord ++ tailWord_1320224).sum := by decide
  have hdescent : baseEnd_1320224 < baseStart_1320224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320252 : List Nat := [2, 2, 2, 2, 1, 4, 3, 6]
def baseStart_1320252 : Nat := 118140960795 + 1320252 * 2 ^ 59
def prefixEnd_1320252 : Nat := 4983230072969 + 3 ^ 40 * 1320252 * 2
def baseEnd_1320252 : Nat := 50216582300731388272465

theorem tailTrace_1320252 : CollatzResearch.WordTrace tailWord_1320252 prefixEnd_1320252 50216582300731388272465 := by
  unfold tailWord_1320252
  simp only [CollatzResearch.WordTrace]
  refine ⟨24076773206479979967621505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32102364275306639956828673 24076773206479979967621505)
  ·
    refine ⟨18057579904859984975716129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24076773206479979967621505 18057579904859984975716129)
    ·
      refine ⟨13543184928644988731787097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18057579904859984975716129 13543184928644988731787097)
      ·
        refine ⟨10157388696483741548840323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13543184928644988731787097 10157388696483741548840323)
        ·
          refine ⟨15236083044725612323260485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10157388696483741548840323 15236083044725612323260485)
          ·
            refine ⟨2856765570886052310611341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15236083044725612323260485 2856765570886052310611341)
            ·
              refine ⟨1071287089082269616479253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2856765570886052310611341 1071287089082269616479253)
              ·
                refine ⟨50216582300731388272465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1071287089082269616479253 50216582300731388272465)
                ·
                  rfl

theorem cell22_1320252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 6].length) (baseStart_1320252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320252 prefixEnd_1320252 := by exact prefixLift 1320252
  have htrace : WordTrace (prefixWord ++ tailWord_1320252) baseStart_1320252 baseEnd_1320252 := by
    simpa [prefixWord, tailWord_1320252, baseEnd_1320252] using wordTrace_append hprefix tailTrace_1320252
  have hstable : (prefixWord ++ tailWord_1320252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320252).length < 2 ^ (prefixWord ++ tailWord_1320252).sum := by decide
  have hdescent : baseEnd_1320252 < baseStart_1320252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320269 : List Nat := [1, 6, 1, 3, 1, 1, 9]
def baseStart_1320269 : Nat := 118140960795 + 1320269 * 2 ^ 59
def prefixEnd_1320269 : Nat := 4983230072969 + 3 ^ 40 * 1320269 * 2
def baseEnd_1320269 : Nat := 16739076302000004325079

theorem tailTrace_1320269 : CollatzResearch.WordTrace tailWord_1320269 prefixEnd_1320269 16739076302000004325079 := by
  unfold tailWord_1320269
  simp only [CollatzResearch.WordTrace]
  refine ⟨48154166453898371838611861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32102777635932247892407907 48154166453898371838611861)
  ·
    refine ⟨2257226552526486179934931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48154166453898371838611861 2257226552526486179934931)
    ·
      refine ⟨3385839828789729269902397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2257226552526486179934931 3385839828789729269902397)
      ·
        refine ⟨1269689935796148476213399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3385839828789729269902397 1269689935796148476213399)
        ·
          refine ⟨1904534903694222714320099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269689935796148476213399 1904534903694222714320099)
          ·
            refine ⟨2856802355541334071480149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904534903694222714320099 2856802355541334071480149)
            ·
              refine ⟨16739076302000004325079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2856802355541334071480149 16739076302000004325079)
              ·
                rfl

theorem cell22_1320269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 9].length) (baseStart_1320269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320269 prefixEnd_1320269 := by exact prefixLift 1320269
  have htrace : WordTrace (prefixWord ++ tailWord_1320269) baseStart_1320269 baseEnd_1320269 := by
    simpa [prefixWord, tailWord_1320269, baseEnd_1320269] using wordTrace_append hprefix tailTrace_1320269
  have hstable : (prefixWord ++ tailWord_1320269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320269).length < 2 ^ (prefixWord ++ tailWord_1320269).sum := by decide
  have hdescent : baseEnd_1320269 < baseStart_1320269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320280 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 7]
def baseStart_1320280 : Nat := 118140960795 + 1320280 * 2 ^ 59
def prefixEnd_1320280 : Nat := 4983230072969 + 3 ^ 40 * 1320280 * 2
def baseEnd_1320280 : Nat := 150652941892933251584033

theorem tailTrace_1320280 : CollatzResearch.WordTrace tailWord_1320280 prefixEnd_1320280 150652941892933251584033 := by
  unfold tailWord_1320280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24077283828429260358631147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32103045104572347144841529 24077283828429260358631147)
  ·
    refine ⟨36115925742643890537946721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24077283828429260358631147 36115925742643890537946721)
    ·
      refine ⟨27086944306982917903460041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36115925742643890537946721 27086944306982917903460041)
      ·
        refine ⟨20315208230237188427595031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27086944306982917903460041 20315208230237188427595031)
        ·
          refine ⟨30472812345355782641392547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20315208230237188427595031 30472812345355782641392547)
          ·
            refine ⟨45709218518033673962088821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30472812345355782641392547 45709218518033673962088821)
            ·
              refine ⟨4285239236065656933945827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45709218518033673962088821 4285239236065656933945827)
              ·
                refine ⟨6427858854098485400918741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4285239236065656933945827 6427858854098485400918741)
                ·
                  refine ⟨150652941892933251584033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6427858854098485400918741 150652941892933251584033)
                  ·
                    rfl

theorem cell22_1320280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_1320280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320280 prefixEnd_1320280 := by exact prefixLift 1320280
  have htrace : WordTrace (prefixWord ++ tailWord_1320280) baseStart_1320280 baseEnd_1320280 := by
    simpa [prefixWord, tailWord_1320280, baseEnd_1320280] using wordTrace_append hprefix tailTrace_1320280
  have hstable : (prefixWord ++ tailWord_1320280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320280).length < 2 ^ (prefixWord ++ tailWord_1320280).sum := by decide
  have hdescent : baseEnd_1320280 < baseStart_1320280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320325 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 8]
def baseStart_1320325 : Nat := 118140960795 + 1320325 * 2 ^ 59
def prefixEnd_1320325 : Nat := 4983230072969 + 3 ^ 40 * 1320325 * 2
def baseEnd_1320325 : Nat := 150658076699478212458987

theorem tailTrace_1320325 : CollatzResearch.WordTrace tailWord_1320325 prefixEnd_1320325 150658076699478212458987 := by
  unfold tailWord_1320325
  simp only [CollatzResearch.WordTrace]
  refine ⟨48156208941695493402650429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32104139294463662268433619 48156208941695493402650429)
  ·
    refine ⟨18058578353135810025993911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48156208941695493402650429 18058578353135810025993911)
    ·
      refine ⟨27087867529703715038990867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18058578353135810025993911 27087867529703715038990867)
      ·
        refine ⟨40631801294555572558486301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27087867529703715038990867 40631801294555572558486301)
        ·
          refine ⟨15236925485458339709432363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40631801294555572558486301 15236925485458339709432363)
          ·
            refine ⟨22855388228187509564148545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15236925485458339709432363 22855388228187509564148545)
            ·
              refine ⟨17141541171140632173111409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22855388228187509564148545 17141541171140632173111409)
              ·
                refine ⟨12856155878355474129833557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17141541171140632173111409 12856155878355474129833557)
                ·
                  refine ⟨150658076699478212458987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12856155878355474129833557 150658076699478212458987)
                  ·
                    rfl

theorem cell22_1320325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_1320325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320325 prefixEnd_1320325 := by exact prefixLift 1320325
  have htrace : WordTrace (prefixWord ++ tailWord_1320325) baseStart_1320325 baseEnd_1320325 := by
    simpa [prefixWord, tailWord_1320325, baseEnd_1320325] using wordTrace_append hprefix tailTrace_1320325
  have hstable : (prefixWord ++ tailWord_1320325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320325).length < 2 ^ (prefixWord ++ tailWord_1320325).sum := by decide
  have hdescent : baseEnd_1320325 < baseStart_1320325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320348 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 5]
def baseStart_1320348 : Nat := 118140960795 + 1320348 * 2 ^ 59
def prefixEnd_1320348 : Nat := 4983230072969 + 3 ^ 40 * 1320348 * 2
def baseEnd_1320348 : Nat := 150660701156156748017297

theorem tailTrace_1320348 : CollatzResearch.WordTrace tailWord_1320348 prefixEnd_1320348 150660701156156748017297 := by
  unfold tailWord_1320348
  simp only [CollatzResearch.WordTrace]
  refine ⟨24078523910306084165368849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32104698547074778887158465 24078523910306084165368849)
  ·
    refine ⟨18058892932729563124026637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24078523910306084165368849 18058892932729563124026637)
    ·
      refine ⟨6772084849773586171509989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18058892932729563124026637 6772084849773586171509989)
      ·
        refine ⟨1269765909332547407158123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6772084849773586171509989 1269765909332547407158123)
        ·
          refine ⟨1904648863998821110737185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269765909332547407158123 1904648863998821110737185)
          ·
            refine ⟨1428486647999115833052889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904648863998821110737185 1428486647999115833052889)
            ·
              refine ⟨1071364985999336874789667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428486647999115833052889 1071364985999336874789667)
              ·
                refine ⟨1607047478999005312184501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071364985999336874789667 1607047478999005312184501)
                ·
                  refine ⟨150660701156156748017297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1607047478999005312184501 150660701156156748017297)
                  ·
                    rfl

theorem cell22_1320348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_1320348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320348 prefixEnd_1320348 := by exact prefixLift 1320348
  have htrace : WordTrace (prefixWord ++ tailWord_1320348) baseStart_1320348 baseEnd_1320348 := by
    simpa [prefixWord, tailWord_1320348, baseEnd_1320348] using wordTrace_append hprefix tailTrace_1320348
  have hstable : (prefixWord ++ tailWord_1320348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320348).length < 2 ^ (prefixWord ++ tailWord_1320348).sum := by decide
  have hdescent : baseEnd_1320348 < baseStart_1320348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320357 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_1320357 : Nat := 118140960795 + 1320357 * 2 ^ 59
def prefixEnd_1320357 : Nat := 4983230072969 + 3 ^ 40 * 1320357 * 2
def baseEnd_1320357 : Nat := 451985184352397220576863

theorem tailTrace_1320357 : CollatzResearch.WordTrace tailWord_1320357 prefixEnd_1320357 451985184352397220576863 := by
  unfold tailWord_1320357
  simp only [CollatzResearch.WordTrace]
  refine ⟨48157376077579562867815325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32104917385053041911876883 48157376077579562867815325)
  ·
    refine ⟨18059016029092336075430747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48157376077579562867815325 18059016029092336075430747)
    ·
      refine ⟨27088524043638504113146121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18059016029092336075430747 27088524043638504113146121)
      ·
        refine ⟨20316393032728878084859591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27088524043638504113146121 20316393032728878084859591)
        ·
          refine ⟨30474589549093317127289387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20316393032728878084859591 30474589549093317127289387)
          ·
            refine ⟨45711884323639975690934081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30474589549093317127289387 45711884323639975690934081)
            ·
              refine ⟨34283913242729981768200561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45711884323639975690934081 34283913242729981768200561)
              ·
                refine ⟨25712934932047486326150421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34283913242729981768200561 25712934932047486326150421)
                ·
                  refine ⟨1205293824939725921538301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25712934932047486326150421 1205293824939725921538301)
                  ·
                    refine ⟨451985184352397220576863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205293824939725921538301 451985184352397220576863)
                    ·
                      rfl

theorem cell22_1320357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_1320357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320357 prefixEnd_1320357 := by exact prefixLift 1320357
  have htrace : WordTrace (prefixWord ++ tailWord_1320357) baseStart_1320357 baseEnd_1320357 := by
    simpa [prefixWord, tailWord_1320357, baseEnd_1320357] using wordTrace_append hprefix tailTrace_1320357
  have hstable : (prefixWord ++ tailWord_1320357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320357).length < 2 ^ (prefixWord ++ tailWord_1320357).sum := by decide
  have hdescent : baseEnd_1320357 < baseStart_1320357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320386 : List Nat := [3, 5, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1320386 : Nat := 118140960795 + 1320386 * 2 ^ 59
def prefixEnd_1320386 : Nat := 4983230072969 + 3 ^ 40 * 1320386 * 2
def baseEnd_1320386 : Nat := 451995111645050811601775

theorem tailTrace_1320386 : CollatzResearch.WordTrace tailWord_1320386 prefixEnd_1320386 451995111645050811601775 := by
  unfold tailWord_1320386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12039608448618625205155253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32105622529649667213747341 12039608448618625205155253)
  ·
    refine ⟨1128713292057996112983305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12039608448618625205155253 1128713292057996112983305)
    ·
      refine ⟨846534969043497084737479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1128713292057996112983305 846534969043497084737479)
      ·
        refine ⟨1269802453565245627106219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846534969043497084737479 1269802453565245627106219)
        ·
          refine ⟨1904703680347868440659329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269802453565245627106219 1904703680347868440659329)
          ·
            refine ⟨1428527760260901330494497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904703680347868440659329 1428527760260901330494497)
            ·
              refine ⟨1071395820195675997870873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428527760260901330494497 1071395820195675997870873)
              ·
                refine ⟨803546865146756998403155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071395820195675997870873 803546865146756998403155)
                ·
                  refine ⟨1205320297720135497604733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803546865146756998403155 1205320297720135497604733)
                  ·
                    refine ⟨451995111645050811601775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205320297720135497604733 451995111645050811601775)
                    ·
                      rfl

theorem cell22_1320386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1320386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320386 prefixEnd_1320386 := by exact prefixLift 1320386
  have htrace : WordTrace (prefixWord ++ tailWord_1320386) baseStart_1320386 baseEnd_1320386 := by
    simpa [prefixWord, tailWord_1320386, baseEnd_1320386] using wordTrace_append hprefix tailTrace_1320386
  have hstable : (prefixWord ++ tailWord_1320386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320386).length < 2 ^ (prefixWord ++ tailWord_1320386).sum := by decide
  have hdescent : baseEnd_1320386 < baseStart_1320386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320419 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 5, 3]
def baseStart_1320419 : Nat := 118140960795 + 1320419 * 2 ^ 59
def prefixEnd_1320419 : Nat := 4983230072969 + 3 ^ 40 * 1320419 * 2
def baseEnd_1320419 : Nat := 452006408219449725526673

theorem tailTrace_1320419 : CollatzResearch.WordTrace tailWord_1320419 prefixEnd_1320419 452006408219449725526673 := by
  unfold tailWord_1320419
  simp only [CollatzResearch.WordTrace]
  refine ⟨48159637403354947456572311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32106424935569964971048207 48159637403354947456572311)
  ·
    refine ⟨72239456105032421184858467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48159637403354947456572311 72239456105032421184858467)
    ·
      refine ⟨108359184157548631777287701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72239456105032421184858467 108359184157548631777287701)
      ·
        refine ⟨5079336757385092114560361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108359184157548631777287701 5079336757385092114560361)
        ·
          refine ⟨3809502568038819085920271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5079336757385092114560361 3809502568038819085920271)
          ·
            refine ⟨5714253852058228628880407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809502568038819085920271 5714253852058228628880407)
            ·
              refine ⟨8571380778087342943320611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5714253852058228628880407 8571380778087342943320611)
              ·
                refine ⟨12857071167131014414980917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8571380778087342943320611 12857071167131014414980917)
                ·
                  refine ⟨1205350421918532601404461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12857071167131014414980917 1205350421918532601404461)
                  ·
                    refine ⟨452006408219449725526673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205350421918532601404461 452006408219449725526673)
                    ·
                      rfl

theorem cell22_1320419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 3].length) (baseStart_1320419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320419 prefixEnd_1320419 := by exact prefixLift 1320419
  have htrace : WordTrace (prefixWord ++ tailWord_1320419) baseStart_1320419 baseEnd_1320419 := by
    simpa [prefixWord, tailWord_1320419, baseEnd_1320419] using wordTrace_append hprefix tailTrace_1320419
  have hstable : (prefixWord ++ tailWord_1320419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320419).length < 2 ^ (prefixWord ++ tailWord_1320419).sum := by decide
  have hdescent : baseEnd_1320419 < baseStart_1320419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320449 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 7]
def baseStart_1320449 : Nat := 118140960795 + 1320449 * 2 ^ 59
def prefixEnd_1320449 : Nat := 4983230072969 + 3 ^ 40 * 1320449 * 2
def baseEnd_1320449 : Nat := 150672225944179882425527

theorem tailTrace_1320449 : CollatzResearch.WordTrace tailWord_1320449 prefixEnd_1320449 150672225944179882425527 := by
  unfold tailWord_1320449
  simp only [CollatzResearch.WordTrace]
  refine ⟨48160731593246262580164401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32107154395497508386776267 48160731593246262580164401)
  ·
    refine ⟨36120548694934696935123301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48160731593246262580164401 36120548694934696935123301)
    ·
      refine ⟨6772602880300255675335619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36120548694934696935123301 6772602880300255675335619)
      ·
        refine ⟨10158904320450383513003429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772602880300255675335619 10158904320450383513003429)
        ·
          refine ⟨1904794560084446908688143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10158904320450383513003429 1904794560084446908688143)
          ·
            refine ⟨2857191840126670363032215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904794560084446908688143 2857191840126670363032215)
            ·
              refine ⟨4285787760190005544548323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857191840126670363032215 4285787760190005544548323)
              ·
                refine ⟨6428681640285008316822485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4285787760190005544548323 6428681640285008316822485)
                ·
                  refine ⟨150672225944179882425527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6428681640285008316822485 150672225944179882425527)
                  ·
                    rfl

theorem cell22_1320449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_1320449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320449 prefixEnd_1320449 := by exact prefixLift 1320449
  have htrace : WordTrace (prefixWord ++ tailWord_1320449) baseStart_1320449 baseEnd_1320449 := by
    simpa [prefixWord, tailWord_1320449, baseEnd_1320449] using wordTrace_append hprefix tailTrace_1320449
  have hstable : (prefixWord ++ tailWord_1320449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320449).length < 2 ^ (prefixWord ++ tailWord_1320449).sum := by decide
  have hdescent : baseEnd_1320449 < baseStart_1320449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320479 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 1, 4]
def baseStart_1320479 : Nat := 118140960795 + 1320479 * 2 ^ 59
def prefixEnd_1320479 : Nat := 4983230072969 + 3 ^ 40 * 1320479 * 2
def baseEnd_1320479 : Nat := 452026947445629569026489

theorem tailTrace_1320479 : CollatzResearch.WordTrace tailWord_1320479 prefixEnd_1320479 452026947445629569026489 := by
  unfold tailWord_1320479
  simp only [CollatzResearch.WordTrace]
  refine ⟨48161825783137577703756491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32107883855425051802504327 48161825783137577703756491)
  ·
    refine ⟨72242738674706366555634737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48161825783137577703756491 72242738674706366555634737)
    ·
      refine ⟨54182054006029774916726053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72242738674706366555634737 54182054006029774916726053)
      ·
        refine ⟨10159135126130582796886135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54182054006029774916726053 10159135126130582796886135)
        ·
          refine ⟨15238702689195874195329203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10159135126130582796886135 15238702689195874195329203)
          ·
            refine ⟨22858054033793811292993805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15238702689195874195329203 22858054033793811292993805)
            ·
              refine ⟨8571770262672679234872677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22858054033793811292993805 8571770262672679234872677)
              ·
                refine ⟨1607206924251127356538627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8571770262672679234872677 1607206924251127356538627)
                ·
                  refine ⟨2410810386376691034807941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607206924251127356538627 2410810386376691034807941)
                  ·
                    refine ⟨452026947445629569026489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2410810386376691034807941 452026947445629569026489)
                    ·
                      rfl

theorem cell22_1320479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_1320479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320479 prefixEnd_1320479 := by exact prefixLift 1320479
  have htrace : WordTrace (prefixWord ++ tailWord_1320479) baseStart_1320479 baseEnd_1320479 := by
    simpa [prefixWord, tailWord_1320479, baseEnd_1320479] using wordTrace_append hprefix tailTrace_1320479
  have hstable : (prefixWord ++ tailWord_1320479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320479).length < 2 ^ (prefixWord ++ tailWord_1320479).sum := by decide
  have hdescent : baseEnd_1320479 < baseStart_1320479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320537 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_1320537 : Nat := 118140960795 + 1320537 * 2 ^ 59
def prefixEnd_1320537 : Nat := 4983230072969 + 3 ^ 40 * 1320537 * 2
def baseEnd_1320537 : Nat := 452046802030936751076311

theorem tailTrace_1320537 : CollatzResearch.WordTrace tailWord_1320537 prefixEnd_1320537 452046802030936751076311 := by
  unfold tailWord_1320537
  simp only [CollatzResearch.WordTrace]
  refine ⟨48163941216927453609367865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32109294144618302406245243 48163941216927453609367865)
  ·
    refine ⟨36122955912695590207025899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48163941216927453609367865 36122955912695590207025899)
    ·
      refine ⟨54184433869043385310538849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36122955912695590207025899 54184433869043385310538849)
      ·
        refine ⟨40638325401782538982904137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54184433869043385310538849 40638325401782538982904137)
        ·
          refine ⟨30478744051336904237178103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40638325401782538982904137 30478744051336904237178103)
          ·
            refine ⟨45718116077005356355767155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30478744051336904237178103 45718116077005356355767155)
            ·
              refine ⟨68577174115508034533650733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45718116077005356355767155 68577174115508034533650733)
              ·
                refine ⟨25716440293315512950119025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68577174115508034533650733 25716440293315512950119025)
                ·
                  refine ⟨19287330219986634712589269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25716440293315512950119025 19287330219986634712589269)
                  ·
                    refine ⟨452046802030936751076311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19287330219986634712589269 452046802030936751076311)
                    ·
                      rfl

theorem cell22_1320537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_1320537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320537 prefixEnd_1320537 := by exact prefixLift 1320537
  have htrace : WordTrace (prefixWord ++ tailWord_1320537) baseStart_1320537 baseEnd_1320537 := by
    simpa [prefixWord, tailWord_1320537, baseEnd_1320537] using wordTrace_append hprefix tailTrace_1320537
  have hstable : (prefixWord ++ tailWord_1320537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320537).length < 2 ^ (prefixWord ++ tailWord_1320537).sum := by decide
  have hdescent : baseEnd_1320537 < baseStart_1320537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320676 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_1320676 : Nat := 118140960795 + 1320676 * 2 ^ 59
def prefixEnd_1320676 : Nat := 4983230072969 + 3 ^ 40 * 1320676 * 2
def baseEnd_1320676 : Nat := 452094384571586721850885

theorem tailTrace_1320676 : CollatzResearch.WordTrace tailWord_1320676 prefixEnd_1320676 452094384571586721850885 := by
  unfold tailWord_1320676
  simp only [CollatzResearch.WordTrace]
  refine ⟨24084505481711940174338941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32112673975615920232451921 24084505481711940174338941)
  ·
    refine ⟨9031689555641977565377103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24084505481711940174338941 9031689555641977565377103)
    ·
      refine ⟨13547534333462966348065655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9031689555641977565377103 13547534333462966348065655)
      ·
        refine ⟨20321301500194449522098483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13547534333462966348065655 20321301500194449522098483)
        ·
          refine ⟨30481952250291674283147725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20321301500194449522098483 30481952250291674283147725)
          ·
            refine ⟨11430732093859377856180397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30481952250291674283147725 11430732093859377856180397)
            ·
              refine ⟨4286524535197266696067649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11430732093859377856180397 4286524535197266696067649)
              ·
                refine ⟨3214893401397950022050737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4286524535197266696067649 3214893401397950022050737)
                ·
                  refine ⟨2411170051048462516538053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3214893401397950022050737 2411170051048462516538053)
                  ·
                    refine ⟨452094384571586721850885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2411170051048462516538053 452094384571586721850885)
                    ·
                      rfl

theorem cell22_1320676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_1320676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320676 prefixEnd_1320676 := by exact prefixLift 1320676
  have htrace : WordTrace (prefixWord ++ tailWord_1320676) baseStart_1320676 baseEnd_1320676 := by
    simpa [prefixWord, tailWord_1320676, baseEnd_1320676] using wordTrace_append hprefix tailTrace_1320676
  have hstable : (prefixWord ++ tailWord_1320676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320676).length < 2 ^ (prefixWord ++ tailWord_1320676).sum := by decide
  have hdescent : baseEnd_1320676 < baseStart_1320676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320680 : List Nat := [2, 1, 4, 1, 3, 2, 3, 2, 4]
def baseStart_1320680 : Nat := 118140960795 + 1320680 * 2 ^ 59
def prefixEnd_1320680 : Nat := 4983230072969 + 3 ^ 40 * 1320680 * 2
def baseEnd_1320680 : Nat := 150698584617777348250291

theorem tailTrace_1320680 : CollatzResearch.WordTrace tailWord_1320680 prefixEnd_1320680 150698584617777348250291 := by
  unfold tailWord_1320680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24084578427704694515911747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32112771236939592687882329 24084578427704694515911747)
  ·
    refine ⟨36126867641557041773867621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24084578427704694515911747 36126867641557041773867621)
    ·
      refine ⟨6773787682791945332600179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36126867641557041773867621 6773787682791945332600179)
      ·
        refine ⟨10160681524187917998900269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6773787682791945332600179 10160681524187917998900269)
        ·
          refine ⟨3810255571570469249587601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10160681524187917998900269 3810255571570469249587601)
          ·
            refine ⟨2857691678677851937190701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3810255571570469249587601 2857691678677851937190701)
            ·
              refine ⟨1071634379504194476446513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2857691678677851937190701 1071634379504194476446513)
              ·
                refine ⟨803725784628145857334885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071634379504194476446513 803725784628145857334885)
                ·
                  refine ⟨150698584617777348250291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803725784628145857334885 150698584617777348250291)
                  ·
                    rfl

theorem cell22_1320680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_1320680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320680 prefixEnd_1320680 := by exact prefixLift 1320680
  have htrace : WordTrace (prefixWord ++ tailWord_1320680) baseStart_1320680 baseEnd_1320680 := by
    simpa [prefixWord, tailWord_1320680, baseEnd_1320680] using wordTrace_append hprefix tailTrace_1320680
  have hstable : (prefixWord ++ tailWord_1320680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320680).length < 2 ^ (prefixWord ++ tailWord_1320680).sum := by decide
  have hdescent : baseEnd_1320680 < baseStart_1320680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320704 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_1320704 : Nat := 118140960795 + 1320704 * 2 ^ 59
def prefixEnd_1320704 : Nat := 4983230072969 + 3 ^ 40 * 1320704 * 2
def baseEnd_1320704 : Nat := 452103969543803982150799

theorem tailTrace_1320704 : CollatzResearch.WordTrace tailWord_1320704 prefixEnd_1320704 452103969543803982150799 := by
  unfold tailWord_1320704
  simp only [CollatzResearch.WordTrace]
  refine ⟨24085016103661220565348583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32113354804881627420464777 24085016103661220565348583)
  ·
    refine ⟨36127524155491830848022875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24085016103661220565348583 36127524155491830848022875)
    ·
      refine ⟨54191286233237746272034313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36127524155491830848022875 54191286233237746272034313)
      ·
        refine ⟨40643464674928309704025735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54191286233237746272034313 40643464674928309704025735)
        ·
          refine ⟨60965197012392464556038603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40643464674928309704025735 60965197012392464556038603)
          ·
            refine ⟨91447795518588696834057905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60965197012392464556038603 91447795518588696834057905)
            ·
              refine ⟨68585846638941522625543429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91447795518588696834057905 68585846638941522625543429)
              ·
                refine ⟨12859846244801535492289393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68585846638941522625543429 12859846244801535492289393)
                ·
                  refine ⟨9644884683601151619217045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12859846244801535492289393 9644884683601151619217045)
                  ·
                    refine ⟨452103969543803982150799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9644884683601151619217045 452103969543803982150799)
                    ·
                      rfl

theorem cell22_1320704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_1320704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320704 prefixEnd_1320704 := by exact prefixLift 1320704
  have htrace : WordTrace (prefixWord ++ tailWord_1320704) baseStart_1320704 baseEnd_1320704 := by
    simpa [prefixWord, tailWord_1320704, baseEnd_1320704] using wordTrace_append hprefix tailTrace_1320704
  have hstable : (prefixWord ++ tailWord_1320704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320704).length < 2 ^ (prefixWord ++ tailWord_1320704).sum := by decide
  have hdescent : baseEnd_1320704 < baseStart_1320704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320719 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 7]
def baseStart_1320719 : Nat := 118140960795 + 1320719 * 2 ^ 59
def prefixEnd_1320719 : Nat := 4983230072969 + 3 ^ 40 * 1320719 * 2
def baseEnd_1320719 : Nat := 150703034783449647675251

theorem tailTrace_1320719 : CollatzResearch.WordTrace tailWord_1320719 prefixEnd_1320719 150703034783449647675251 := by
  unfold tailWord_1320719
  simp only [CollatzResearch.WordTrace]
  refine ⟨48170579302268098692493211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32113719534845399128328807 48170579302268098692493211)
  ·
    refine ⟨72255868953402148038739817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48170579302268098692493211 72255868953402148038739817)
    ·
      refine ⟨54191901715051611029054863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72255868953402148038739817 54191901715051611029054863)
      ·
        refine ⟨81287852572577416543582295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54191901715051611029054863 81287852572577416543582295)
        ·
          refine ⟨121931778858866124815373443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81287852572577416543582295 121931778858866124815373443)
          ·
            refine ⟨182897668288299187223060165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121931778858866124815373443 182897668288299187223060165)
            ·
              refine ⟨34293312804056097604323781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182897668288299187223060165 34293312804056097604323781)
              ·
                refine ⟨6429996150760518300810709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34293312804056097604323781 6429996150760518300810709)
                ·
                  refine ⟨150703034783449647675251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6429996150760518300810709 150703034783449647675251)
                  ·
                    rfl

theorem cell22_1320719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 7].length) (baseStart_1320719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320719 prefixEnd_1320719 := by exact prefixLift 1320719
  have htrace : WordTrace (prefixWord ++ tailWord_1320719) baseStart_1320719 baseEnd_1320719 := by
    simpa [prefixWord, tailWord_1320719, baseEnd_1320719] using wordTrace_append hprefix tailTrace_1320719
  have hstable : (prefixWord ++ tailWord_1320719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320719).length < 2 ^ (prefixWord ++ tailWord_1320719).sum := by decide
  have hdescent : baseEnd_1320719 < baseStart_1320719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320774 : List Nat := [6, 1, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1320774 : Nat := 118140960795 + 1320774 * 2 ^ 59
def prefixEnd_1320774 : Nat := 4983230072969 + 3 ^ 40 * 1320774 * 2
def baseEnd_1320774 : Nat := 452127931974347132900585

theorem tailTrace_1320774 : CollatzResearch.WordTrace tailWord_1320774 prefixEnd_1320774 452127931974347132900585 := by
  unfold tailWord_1320774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505393291158401346429543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32115056878045895390496917 1505393291158401346429543)
  ·
    refine ⟨2258089936737602019644315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1505393291158401346429543 2258089936737602019644315)
    ·
      refine ⟨3387134905106403029466473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258089936737602019644315 3387134905106403029466473)
      ·
        refine ⟨2540351178829802272099855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3387134905106403029466473 2540351178829802272099855)
        ·
          refine ⟨3810526768244703408149783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540351178829802272099855 3810526768244703408149783)
          ·
            refine ⟨5715790152367055112224675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810526768244703408149783 5715790152367055112224675)
            ·
              refine ⟨8573685228550582668337013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715790152367055112224675 8573685228550582668337013)
              ·
                refine ⟨803782990176617125156595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8573685228550582668337013 803782990176617125156595)
                ·
                  refine ⟨1205674485264925687734893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803782990176617125156595 1205674485264925687734893)
                  ·
                    refine ⟨452127931974347132900585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205674485264925687734893 452127931974347132900585)
                    ·
                      rfl

theorem cell22_1320774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1320774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320774 prefixEnd_1320774 := by exact prefixLift 1320774
  have htrace : WordTrace (prefixWord ++ tailWord_1320774) baseStart_1320774 baseEnd_1320774 := by
    simpa [prefixWord, tailWord_1320774, baseEnd_1320774] using wordTrace_append hprefix tailTrace_1320774
  have hstable : (prefixWord ++ tailWord_1320774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320774).length < 2 ^ (prefixWord ++ tailWord_1320774).sum := by decide
  have hdescent : baseEnd_1320774 < baseStart_1320774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320813 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1320813 : Nat := 118140960795 + 1320813 * 2 ^ 59
def prefixEnd_1320813 : Nat := 4983230072969 + 3 ^ 40 * 1320813 * 2
def baseEnd_1320813 : Nat := 452141282471364031175465

theorem tailTrace_1320813 : CollatzResearch.WordTrace tailWord_1320813 prefixEnd_1320813 452141282471364031175465 := by
  unfold tailWord_1320813
  simp only [CollatzResearch.WordTrace]
  refine ⟨48174007763927552746415093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32116005175951701830943395 48174007763927552746415093)
  ·
    refine ⟨4516313227868208069976415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48174007763927552746415093 4516313227868208069976415)
    ·
      refine ⟨6774469841802312104964623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4516313227868208069976415 6774469841802312104964623)
      ·
        refine ⟨10161704762703468157446935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6774469841802312104964623 10161704762703468157446935)
        ·
          refine ⟨15242557144055202236170403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10161704762703468157446935 15242557144055202236170403)
          ·
            refine ⟨22863835716082803354255605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15242557144055202236170403 22863835716082803354255605)
            ·
              refine ⟨2143484598382762814461463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22863835716082803354255605 2143484598382762814461463)
              ·
                refine ⟨3215226897574144221692195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143484598382762814461463 3215226897574144221692195)
                ·
                  refine ⟨4822840346361216332538293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215226897574144221692195 4822840346361216332538293)
                  ·
                    refine ⟨452141282471364031175465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4822840346361216332538293 452141282471364031175465)
                    ·
                      rfl

theorem cell22_1320813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1320813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320813 prefixEnd_1320813 := by exact prefixLift 1320813
  have htrace : WordTrace (prefixWord ++ tailWord_1320813) baseStart_1320813 baseEnd_1320813 := by
    simpa [prefixWord, tailWord_1320813, baseEnd_1320813] using wordTrace_append hprefix tailTrace_1320813
  have hstable : (prefixWord ++ tailWord_1320813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320813).length < 2 ^ (prefixWord ++ tailWord_1320813).sum := by decide
  have hdescent : baseEnd_1320813 < baseStart_1320813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320963 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 2, 4]
def baseStart_1320963 : Nat := 118140960795 + 1320963 * 2 ^ 59
def prefixEnd_1320963 : Nat := 4983230072969 + 3 ^ 40 * 1320963 * 2
def baseEnd_1320963 : Nat := 452192630536813639925005

theorem tailTrace_1320963 : CollatzResearch.WordTrace tailWord_1320963 prefixEnd_1320963 452192630536813639925005 := by
  unfold tailWord_1320963
  simp only [CollatzResearch.WordTrace]
  refine ⟨48179478713384128364375543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32119652475589418909583695 48179478713384128364375543)
  ·
    refine ⟨72269218070076192546563315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48179478713384128364375543 72269218070076192546563315)
    ·
      refine ⟨108403827105114288819844973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72269218070076192546563315 108403827105114288819844973)
      ·
        refine ⟨40651435164417858307441865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108403827105114288819844973 40651435164417858307441865)
        ·
          refine ⟨30488576373313393730581399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40651435164417858307441865 30488576373313393730581399)
          ·
            refine ⟨45732864559970090595872099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30488576373313393730581399 45732864559970090595872099)
            ·
              refine ⟨68599296839955135893808149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45732864559970090595872099 68599296839955135893808149)
              ·
                refine ⟨3215592039372896995022257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68599296839955135893808149 3215592039372896995022257)
                ·
                  refine ⟨2411694029529672746266693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3215592039372896995022257 2411694029529672746266693)
                  ·
                    refine ⟨452192630536813639925005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2411694029529672746266693 452192630536813639925005)
                    ·
                      rfl

theorem cell22_1320963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_1320963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320963 prefixEnd_1320963 := by exact prefixLift 1320963
  have htrace : WordTrace (prefixWord ++ tailWord_1320963) baseStart_1320963 baseEnd_1320963 := by
    simpa [prefixWord, tailWord_1320963, baseEnd_1320963] using wordTrace_append hprefix tailTrace_1320963
  have hstable : (prefixWord ++ tailWord_1320963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320963).length < 2 ^ (prefixWord ++ tailWord_1320963).sum := by decide
  have hdescent : baseEnd_1320963 < baseStart_1320963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1320965 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_1320965 : Nat := 118140960795 + 1320965 * 2 ^ 59
def prefixEnd_1320965 : Nat := 4983230072969 + 3 ^ 40 * 1320965 * 2
def baseEnd_1320965 : Nat := 452193315177686301374999

theorem tailTrace_1320965 : CollatzResearch.WordTrace tailWord_1320965 prefixEnd_1320965 452193315177686301374999 := by
  unfold tailWord_1320965
  simp only [CollatzResearch.WordTrace]
  refine ⟨48179551659376882705948349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32119701106251255137298899 48179551659376882705948349)
  ·
    refine ⟨18067331872266331014730631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48179551659376882705948349 18067331872266331014730631)
    ·
      refine ⟨27100997808399496522095947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18067331872266331014730631 27100997808399496522095947)
      ·
        refine ⟨40651496712599244783143921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27100997808399496522095947 40651496712599244783143921)
        ·
          refine ⟨30488622534449433587357941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40651496712599244783143921 30488622534449433587357941)
          ·
            refine ⟨2858308362604634398814807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30488622534449433587357941 2858308362604634398814807)
            ·
              refine ⟨4287462543906951598222211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858308362604634398814807 4287462543906951598222211)
              ·
                refine ⟨6431193815860427397333317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287462543906951598222211 6431193815860427397333317)
                ·
                  refine ⟨1205848840473830136999997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6431193815860427397333317 1205848840473830136999997)
                  ·
                    refine ⟨452193315177686301374999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205848840473830136999997 452193315177686301374999)
                    ·
                      rfl

theorem cell22_1320965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_1320965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1320965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1320965 prefixEnd_1320965 := by exact prefixLift 1320965
  have htrace : WordTrace (prefixWord ++ tailWord_1320965) baseStart_1320965 baseEnd_1320965 := by
    simpa [prefixWord, tailWord_1320965, baseEnd_1320965] using wordTrace_append hprefix tailTrace_1320965
  have hstable : (prefixWord ++ tailWord_1320965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1320965).length < 2 ^ (prefixWord ++ tailWord_1320965).sum := by decide
  have hdescent : baseEnd_1320965 < baseStart_1320965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1320965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321012 : List Nat := [2, 5, 1, 2, 2, 2, 8]
def baseStart_1321012 : Nat := 118140960795 + 1321012 * 2 ^ 59
def prefixEnd_1321012 : Nat := 4983230072969 + 3 ^ 40 * 1321012 * 2
def baseEnd_1321012 : Nat := 16748496453266438720365

theorem tailTrace_1321012 : CollatzResearch.WordTrace tailWord_1321012 prefixEnd_1321012 16748496453266438720365 := by
  unfold tailWord_1321012
  simp only [CollatzResearch.WordTrace]
  refine ⟨24090632945103304866454645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32120843926804406488606193 24090632945103304866454645)
  ·
    refine ⟨2258496838603434831230123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24090632945103304866454645 2258496838603434831230123)
    ·
      refine ⟨3387745257905152246845185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258496838603434831230123 3387745257905152246845185)
      ·
        refine ⟨2540808943428864185133889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3387745257905152246845185 2540808943428864185133889)
        ·
          refine ⟨1905606707571648138850417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2540808943428864185133889 1905606707571648138850417)
          ·
            refine ⟨1429205030678736104137813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905606707571648138850417 1429205030678736104137813)
            ·
              refine ⟨16748496453266438720365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1429205030678736104137813 16748496453266438720365)
              ·
                rfl

theorem cell22_1321012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 8].length) (baseStart_1321012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321012 prefixEnd_1321012 := by exact prefixLift 1321012
  have htrace : WordTrace (prefixWord ++ tailWord_1321012) baseStart_1321012 baseEnd_1321012 := by
    simpa [prefixWord, tailWord_1321012, baseEnd_1321012] using wordTrace_append hprefix tailTrace_1321012
  have hstable : (prefixWord ++ tailWord_1321012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321012).length < 2 ^ (prefixWord ++ tailWord_1321012).sum := by decide
  have hdescent : baseEnd_1321012 < baseStart_1321012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321023 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 7]
def baseStart_1321023 : Nat := 118140960795 + 1321023 * 2 ^ 59
def prefixEnd_1321023 : Nat := 4983230072969 + 3 ^ 40 * 1321023 * 2
def baseEnd_1321023 : Nat := 150737723254331161141607

theorem tailTrace_1321023 : CollatzResearch.WordTrace tailWord_1321023 prefixEnd_1321023 150737723254331161141607 := by
  unfold tailWord_1321023
  simp only [CollatzResearch.WordTrace]
  refine ⟨48181667093166758611559723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32121111395444505741039815 48181667093166758611559723)
  ·
    refine ⟨72272500639750137917339585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48181667093166758611559723 72272500639750137917339585)
    ·
      refine ⟨54204375479812603438004689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72272500639750137917339585 54204375479812603438004689)
      ·
        refine ⟨40653281609859452578503517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54204375479812603438004689 40653281609859452578503517)
        ·
          refine ⟨15244980603697294716938819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40653281609859452578503517 15244980603697294716938819)
          ·
            refine ⟨22867470905545942075408229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15244980603697294716938819 22867470905545942075408229)
            ·
              refine ⟨4287650794789864139139043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22867470905545942075408229 4287650794789864139139043)
              ·
                refine ⟨6431476192184796208708565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287650794789864139139043 6431476192184796208708565)
                ·
                  refine ⟨150737723254331161141607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6431476192184796208708565 150737723254331161141607)
                  ·
                    rfl

theorem cell22_1321023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 7].length) (baseStart_1321023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321023 prefixEnd_1321023 := by exact prefixLift 1321023
  have htrace : WordTrace (prefixWord ++ tailWord_1321023) baseStart_1321023 baseEnd_1321023 := by
    simpa [prefixWord, tailWord_1321023, baseEnd_1321023] using wordTrace_append hprefix tailTrace_1321023
  have hstable : (prefixWord ++ tailWord_1321023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321023).length < 2 ^ (prefixWord ++ tailWord_1321023).sum := by decide
  have hdescent : baseEnd_1321023 < baseStart_1321023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321078 : List Nat := [5, 1, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_1321078 : Nat := 118140960795 + 1321078 * 2 ^ 59
def prefixEnd_1321078 : Nat := 4983230072969 + 3 ^ 40 * 1321078 * 2
def baseEnd_1321078 : Nat := 452231997386991673299653

theorem tailTrace_1321078 : CollatzResearch.WordTrace tailWord_1321078 prefixEnd_1321078 452231997386991673299653 := by
  unfold tailWord_1321078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011479569247968937800743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32122448738645002003207925 3011479569247968937800743)
  ·
    refine ⟨4517219353871953406701115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3011479569247968937800743 4517219353871953406701115)
    ·
      refine ⟨6775829030807930110051673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4517219353871953406701115 6775829030807930110051673)
      ·
        refine ⟨5081871773105947582538755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6775829030807930110051673 5081871773105947582538755)
        ·
          refine ⟨7622807659658921373808133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081871773105947582538755 7622807659658921373808133)
          ·
            refine ⟨1429276436186047757589025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7622807659658921373808133 1429276436186047757589025)
            ·
              refine ⟨1071957327139535818191769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429276436186047757589025 1071957327139535818191769)
              ·
                refine ⟨803967995354651863643827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071957327139535818191769 803967995354651863643827)
                ·
                  refine ⟨1205951993031977795465741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803967995354651863643827 1205951993031977795465741)
                  ·
                    refine ⟨452231997386991673299653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205951993031977795465741 452231997386991673299653)
                    ·
                      rfl

theorem cell22_1321078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_1321078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321078 prefixEnd_1321078 := by exact prefixLift 1321078
  have htrace : WordTrace (prefixWord ++ tailWord_1321078) baseStart_1321078 baseEnd_1321078 := by
    simpa [prefixWord, tailWord_1321078, baseEnd_1321078] using wordTrace_append hprefix tailTrace_1321078
  have hstable : (prefixWord ++ tailWord_1321078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321078).length < 2 ^ (prefixWord ++ tailWord_1321078).sum := by decide
  have hdescent : baseEnd_1321078 < baseStart_1321078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321100 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_1321100 : Nat := 118140960795 + 1321100 * 2 ^ 59
def prefixEnd_1321100 : Nat := 4983230072969 + 3 ^ 40 * 1321100 * 2
def baseEnd_1321100 : Nat := 452239528436590949249585

theorem tailTrace_1321100 : CollatzResearch.WordTrace tailWord_1321100 prefixEnd_1321100 452239528436590949249585 := by
  unfold tailWord_1321100
  simp only [CollatzResearch.WordTrace]
  refine ⟨24092237756943900381056377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32122983675925200508075169 24092237756943900381056377)
  ·
    refine ⟨18069178317707925285792283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24092237756943900381056377 18069178317707925285792283)
    ·
      refine ⟨27103767476561887928688425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18069178317707925285792283 27103767476561887928688425)
      ·
        refine ⟨20327825607421415946516319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27103767476561887928688425 20327825607421415946516319)
        ·
          refine ⟨30491738411132123919774479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20327825607421415946516319 30491738411132123919774479)
          ·
            refine ⟨45737607616698185879661719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30491738411132123919774479 45737607616698185879661719)
            ·
              refine ⟨68606411425047278819492579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45737607616698185879661719 68606411425047278819492579)
              ·
                refine ⟨102909617137570918229238869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68606411425047278819492579 102909617137570918229238869)
                ·
                  refine ⟨1205972075830909197998893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 102909617137570918229238869 1205972075830909197998893)
                  ·
                    refine ⟨452239528436590949249585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205972075830909197998893 452239528436590949249585)
                    ·
                      rfl

theorem cell22_1321100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_1321100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321100 prefixEnd_1321100 := by exact prefixLift 1321100
  have htrace : WordTrace (prefixWord ++ tailWord_1321100) baseStart_1321100 baseEnd_1321100 := by
    simpa [prefixWord, tailWord_1321100, baseEnd_1321100] using wordTrace_append hprefix tailTrace_1321100
  have hstable : (prefixWord ++ tailWord_1321100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321100).length < 2 ^ (prefixWord ++ tailWord_1321100).sum := by decide
  have hdescent : baseEnd_1321100 < baseStart_1321100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321102 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1321102 : Nat := 118140960795 + 1321102 * 2 ^ 59
def prefixEnd_1321102 : Nat := 4983230072969 + 3 ^ 40 * 1321102 * 2
def baseEnd_1321102 : Nat := 150746737692487870233193

theorem tailTrace_1321102 : CollatzResearch.WordTrace tailWord_1321102 prefixEnd_1321102 150746737692487870233193 := by
  unfold tailWord_1321102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6023068557485069387960695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32123032306587036735790373 6023068557485069387960695)
  ·
    refine ⟨9034602836227604081941043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6023068557485069387960695 9034602836227604081941043)
    ·
      refine ⟨13551904254341406122911565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9034602836227604081941043 13551904254341406122911565)
      ·
        refine ⟨5081964095378027296091837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13551904254341406122911565 5081964095378027296091837)
        ·
          refine ⟨1905736535766760236034439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5081964095378027296091837 1905736535766760236034439)
          ·
            refine ⟨2858604803650140354051659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905736535766760236034439 2858604803650140354051659)
            ·
              refine ⟨4287907205475210531077489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858604803650140354051659 4287907205475210531077489)
              ·
                refine ⟨3215930404106407898308117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4287907205475210531077489 3215930404106407898308117)
                ·
                  refine ⟨150746737692487870233193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3215930404106407898308117 150746737692487870233193)
                  ·
                    rfl

theorem cell22_1321102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1321102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321102 prefixEnd_1321102 := by exact prefixLift 1321102
  have htrace : WordTrace (prefixWord ++ tailWord_1321102) baseStart_1321102 baseEnd_1321102 := by
    simpa [prefixWord, tailWord_1321102, baseEnd_1321102] using wordTrace_append hprefix tailTrace_1321102
  have hstable : (prefixWord ++ tailWord_1321102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321102).length < 2 ^ (prefixWord ++ tailWord_1321102).sum := by decide
  have hdescent : baseEnd_1321102 < baseStart_1321102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321113 : List Nat := [1, 2, 1, 2, 1, 2, 1, 12]
def baseStart_1321113 : Nat := 118140960795 + 1321113 * 2 ^ 59
def prefixEnd_1321113 : Nat := 4983230072969 + 3 ^ 40 * 1321113 * 2
def baseEnd_1321113 : Nat := 50249330955807027630505

theorem tailTrace_1321113 : CollatzResearch.WordTrace tailWord_1321113 prefixEnd_1321113 50249330955807027630505 := by
  unfold tailWord_1321113
  simp only [CollatzResearch.WordTrace]
  refine ⟨48184949662840703982335993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32123299775227135988223995 48184949662840703982335993)
  ·
    refine ⟨36138712247130527986751995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48184949662840703982335993 36138712247130527986751995)
    ·
      refine ⟨54208068370695791980127993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36138712247130527986751995 54208068370695791980127993)
      ·
        refine ⟨40656051278021843985095995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54208068370695791980127993 40656051278021843985095995)
        ·
          refine ⟨60984076917032765977643993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40656051278021843985095995 60984076917032765977643993)
          ·
            refine ⟨45738057687774574483232995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60984076917032765977643993 45738057687774574483232995)
            ·
              refine ⟨68607086531661861724849493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45738057687774574483232995 68607086531661861724849493)
              ·
                refine ⟨50249330955807027630505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 68607086531661861724849493 50249330955807027630505)
                ·
                  rfl

theorem cell22_1321113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 12].length) (baseStart_1321113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321113 prefixEnd_1321113 := by exact prefixLift 1321113
  have htrace : WordTrace (prefixWord ++ tailWord_1321113) baseStart_1321113 baseEnd_1321113 := by
    simpa [prefixWord, tailWord_1321113, baseEnd_1321113] using wordTrace_append hprefix tailTrace_1321113
  have hstable : (prefixWord ++ tailWord_1321113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321113).length < 2 ^ (prefixWord ++ tailWord_1321113).sum := by decide
  have hdescent : baseEnd_1321113 < baseStart_1321113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321119 : List Nat := [1, 1, 2, 6, 1, 2, 2, 3, 4]
def baseStart_1321119 : Nat := 118140960795 + 1321119 * 2 ^ 59
def prefixEnd_1321119 : Nat := 4983230072969 + 3 ^ 40 * 1321119 * 2
def baseEnd_1321119 : Nat := 150748677508293744341509

theorem tailTrace_1321119 : CollatzResearch.WordTrace tailWord_1321119 prefixEnd_1321119 150748677508293744341509 := by
  unfold tailWord_1321119
  simp only [CollatzResearch.WordTrace]
  refine ⟨48185168500818967007054411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32123445667212644671369607 48185168500818967007054411)
  ·
    refine ⟨72277752751228450510581617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48185168500818967007054411 72277752751228450510581617)
    ·
      refine ⟨54208314563421337882936213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72277752751228450510581617 54208314563421337882936213)
      ·
        refine ⟨2541014745160375213262635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54208314563421337882936213 2541014745160375213262635)
        ·
          refine ⟨3811522117740562819893953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541014745160375213262635 3811522117740562819893953)
          ·
            refine ⟨2858641588305422114920465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3811522117740562819893953 2858641588305422114920465)
            ·
              refine ⟨2143981191229066586190349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858641588305422114920465 2143981191229066586190349)
              ·
                refine ⟨803992946710899969821381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143981191229066586190349 803992946710899969821381)
                ·
                  refine ⟨150748677508293744341509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803992946710899969821381 150748677508293744341509)
                  ·
                    rfl

theorem cell22_1321119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 4].length) (baseStart_1321119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321119 prefixEnd_1321119 := by exact prefixLift 1321119
  have htrace : WordTrace (prefixWord ++ tailWord_1321119) baseStart_1321119 baseEnd_1321119 := by
    simpa [prefixWord, tailWord_1321119, baseEnd_1321119] using wordTrace_append hprefix tailTrace_1321119
  have hstable : (prefixWord ++ tailWord_1321119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321119).length < 2 ^ (prefixWord ++ tailWord_1321119).sum := by decide
  have hdescent : baseEnd_1321119 < baseStart_1321119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321162 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_1321162 : Nat := 118140960795 + 1321162 * 2 ^ 59
def prefixEnd_1321162 : Nat := 4983230072969 + 3 ^ 40 * 1321162 * 2
def baseEnd_1321162 : Nat := 452260752303643454199395

theorem tailTrace_1321162 : CollatzResearch.WordTrace tailWord_1321162 prefixEnd_1321162 452260752303643454199395 := by
  unfold tailWord_1321162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12046684209915796337717435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32124491226442123567246493 12046684209915796337717435)
  ·
    refine ⟨18070026314873694506576153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12046684209915796337717435 18070026314873694506576153)
    ·
      refine ⟨13552519736155270879932115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18070026314873694506576153 13552519736155270879932115)
      ·
        refine ⟨20328779604232906319898173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13552519736155270879932115 20328779604232906319898173)
        ·
          refine ⟨7623292351587339869961815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20328779604232906319898173 7623292351587339869961815)
          ·
            refine ⟨11434938527381009804942723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623292351587339869961815 11434938527381009804942723)
            ·
              refine ⟨17152407791071514707414085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11434938527381009804942723 17152407791071514707414085)
              ·
                refine ⟨3216076460825909007640141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17152407791071514707414085 3216076460825909007640141)
                ·
                  refine ⟨1206028672809715877865053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3216076460825909007640141 1206028672809715877865053)
                  ·
                    refine ⟨452260752303643454199395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1206028672809715877865053 452260752303643454199395)
                    ·
                      rfl

theorem cell22_1321162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_1321162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321162 prefixEnd_1321162 := by exact prefixLift 1321162
  have htrace : WordTrace (prefixWord ++ tailWord_1321162) baseStart_1321162 baseEnd_1321162 := by
    simpa [prefixWord, tailWord_1321162, baseEnd_1321162] using wordTrace_append hprefix tailTrace_1321162
  have hstable : (prefixWord ++ tailWord_1321162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321162).length < 2 ^ (prefixWord ++ tailWord_1321162).sum := by decide
  have hdescent : baseEnd_1321162 < baseStart_1321162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321196 : List Nat := [2, 2, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_1321196 : Nat := 118140960795 + 1321196 * 2 ^ 59
def prefixEnd_1321196 : Nat := 4983230072969 + 3 ^ 40 * 1321196 * 2
def baseEnd_1321196 : Nat := 452272391198478698849291

theorem tailTrace_1321196 : CollatzResearch.WordTrace tailWord_1321196 prefixEnd_1321196 452272391198478698849291 := by
  unfold tailWord_1321196
  simp only [CollatzResearch.WordTrace]
  refine ⟨24093988460770004578803721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32125317947693339438404961 24093988460770004578803721)
  ·
    refine ⟨18070491345577503434102791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24093988460770004578803721 18070491345577503434102791)
    ·
      refine ⟨27105737018366255151154187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18070491345577503434102791 27105737018366255151154187)
      ·
        refine ⟨40658605527549382726731281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27105737018366255151154187 40658605527549382726731281)
        ·
          refine ⟨30493954145662037045048461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40658605527549382726731281 30493954145662037045048461)
          ·
            refine ⟨11435232804623263891893173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30493954145662037045048461 11435232804623263891893173)
            ·
              refine ⟨1072053075433430989864985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11435232804623263891893173 1072053075433430989864985)
              ·
                refine ⟨804039806575073242398739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072053075433430989864985 804039806575073242398739)
                ·
                  refine ⟨1206059709862609863598109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804039806575073242398739 1206059709862609863598109)
                  ·
                    refine ⟨452272391198478698849291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1206059709862609863598109 452272391198478698849291)
                    ·
                      rfl

theorem cell22_1321196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_1321196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321196 prefixEnd_1321196 := by exact prefixLift 1321196
  have htrace : WordTrace (prefixWord ++ tailWord_1321196) baseStart_1321196 baseEnd_1321196 := by
    simpa [prefixWord, tailWord_1321196, baseEnd_1321196] using wordTrace_append hprefix tailTrace_1321196
  have hstable : (prefixWord ++ tailWord_1321196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321196).length < 2 ^ (prefixWord ++ tailWord_1321196).sum := by decide
  have hdescent : baseEnd_1321196 < baseStart_1321196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321269 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1321269 : Nat := 118140960795 + 1321269 * 2 ^ 59
def prefixEnd_1321269 : Nat := 4983230072969 + 3 ^ 40 * 1321269 * 2
def baseEnd_1321269 : Nat := 452297380590330841774067

theorem tailTrace_1321269 : CollatzResearch.WordTrace tailWord_1321269 prefixEnd_1321269 452297380590330841774067 := by
  unfold tailWord_1321269
  simp only [CollatzResearch.WordTrace]
  refine ⟨48190639450275542625014861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32127092966850361750009907 48190639450275542625014861)
  ·
    refine ⟨18071489793853328484380573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48190639450275542625014861 18071489793853328484380573)
    ·
      refine ⟨6776808672694998181642715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18071489793853328484380573 6776808672694998181642715)
      ·
        refine ⟨10165213009042497272464073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6776808672694998181642715 10165213009042497272464073)
        ·
          refine ⟨7623909756781872954348055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10165213009042497272464073 7623909756781872954348055)
          ·
            refine ⟨11435864635172809431522083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623909756781872954348055 11435864635172809431522083)
            ·
              refine ⟨17153796952759214147283125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435864635172809431522083 17153796952759214147283125)
              ·
                refine ⟨1608168464321176326307793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17153796952759214147283125 1608168464321176326307793)
                ·
                  refine ⟨1206126348240882244730845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1608168464321176326307793 1206126348240882244730845)
                  ·
                    refine ⟨452297380590330841774067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1206126348240882244730845 452297380590330841774067)
                    ·
                      rfl

theorem cell22_1321269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1321269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321269 prefixEnd_1321269 := by exact prefixLift 1321269
  have htrace : WordTrace (prefixWord ++ tailWord_1321269) baseStart_1321269 baseEnd_1321269 := by
    simpa [prefixWord, tailWord_1321269, baseEnd_1321269] using wordTrace_append hprefix tailTrace_1321269
  have hstable : (prefixWord ++ tailWord_1321269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321269).length < 2 ^ (prefixWord ++ tailWord_1321269).sum := by decide
  have hdescent : baseEnd_1321269 < baseStart_1321269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321280 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_1321280 : Nat := 118140960795 + 1321280 * 2 ^ 59
def prefixEnd_1321280 : Nat := 4983230072969 + 3 ^ 40 * 1321280 * 2
def baseEnd_1321280 : Nat := 452301146115130479749033

theorem tailTrace_1321280 : CollatzResearch.WordTrace tailWord_1321280 prefixEnd_1321280 452301146115130479749033 := by
  unfold tailWord_1321280
  simp only [CollatzResearch.WordTrace]
  refine ⟨24095520326617845751832647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32127360435490461002443529 24095520326617845751832647)
  ·
    refine ⟨36143280489926768627748971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24095520326617845751832647 36143280489926768627748971)
    ·
      refine ⟨54214920734890152941623457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36143280489926768627748971 54214920734890152941623457)
      ·
        refine ⟨40661190551167614706217593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54214920734890152941623457 40661190551167614706217593)
        ·
          refine ⟨30495892913375711029663195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40661190551167614706217593 30495892913375711029663195)
          ·
            refine ⟨45743839370063566544494793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30495892913375711029663195 45743839370063566544494793)
            ·
              refine ⟨34307879527547674908371095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45743839370063566544494793 34307879527547674908371095)
              ·
                refine ⟨51461819291321512362556643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34307879527547674908371095 51461819291321512362556643)
                ·
                  refine ⟨77192728936982268543834965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51461819291321512362556643 77192728936982268543834965)
                  ·
                    refine ⟨452301146115130479749033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 77192728936982268543834965 452301146115130479749033)
                    ·
                      rfl

theorem cell22_1321280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_1321280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321280 prefixEnd_1321280 := by exact prefixLift 1321280
  have htrace : WordTrace (prefixWord ++ tailWord_1321280) baseStart_1321280 baseEnd_1321280 := by
    simpa [prefixWord, tailWord_1321280, baseEnd_1321280] using wordTrace_append hprefix tailTrace_1321280
  have hstable : (prefixWord ++ tailWord_1321280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321280).length < 2 ^ (prefixWord ++ tailWord_1321280).sum := by decide
  have hdescent : baseEnd_1321280 < baseStart_1321280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321295 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 8]
def baseStart_1321295 : Nat := 118140960795 + 1321295 * 2 ^ 59
def prefixEnd_1321295 : Nat := 4983230072969 + 3 ^ 40 * 1321295 * 2
def baseEnd_1321295 : Nat := 452306280921675440623987

theorem tailTrace_1321295 : CollatzResearch.WordTrace tailWord_1321295 prefixEnd_1321295 452306280921675440623987 := by
  unfold tailWord_1321295
  simp only [CollatzResearch.WordTrace]
  refine ⟨48191587748181349065461339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32127725165454232710307559 48191587748181349065461339)
  ·
    refine ⟨72287381622272023598192009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48191587748181349065461339 72287381622272023598192009)
    ·
      refine ⟨54215536216704017698644007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72287381622272023598192009 54215536216704017698644007)
      ·
        refine ⟨81323304325056026547966011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54215536216704017698644007 81323304325056026547966011)
        ·
          refine ⟨121984956487584039821949017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81323304325056026547966011 121984956487584039821949017)
          ·
            refine ⟨91488717365688029866461763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121984956487584039821949017 91488717365688029866461763)
            ·
              refine ⟨137233076048532044799692645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91488717365688029866461763 137233076048532044799692645)
              ·
                refine ⟨25731201759099758399942371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137233076048532044799692645 25731201759099758399942371)
                ·
                  refine ⟨38596802638649637599913557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25731201759099758399942371 38596802638649637599913557)
                  ·
                    refine ⟨452306280921675440623987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38596802638649637599913557 452306280921675440623987)
                    ·
                      rfl

theorem cell22_1321295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_1321295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321295 prefixEnd_1321295 := by exact prefixLift 1321295
  have htrace : WordTrace (prefixWord ++ tailWord_1321295) baseStart_1321295 baseEnd_1321295 := by
    simpa [prefixWord, tailWord_1321295, baseEnd_1321295] using wordTrace_append hprefix tailTrace_1321295
  have hstable : (prefixWord ++ tailWord_1321295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321295).length < 2 ^ (prefixWord ++ tailWord_1321295).sum := by decide
  have hdescent : baseEnd_1321295 < baseStart_1321295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321402 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_1321402 : Nat := 118140960795 + 1321402 * 2 ^ 59
def prefixEnd_1321402 : Nat := 4983230072969 + 3 ^ 40 * 1321402 * 2
def baseEnd_1321402 : Nat := 452342909208362828198659

theorem tailTrace_1321402 : CollatzResearch.WordTrace tailWord_1321402 prefixEnd_1321402 452342909208362828198659 := by
  unfold tailWord_1321402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12048872589698426584901615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32130326905862470893070973 12048872589698426584901615)
  ·
    refine ⟨18073308884547639877352423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12048872589698426584901615 18073308884547639877352423)
    ·
      refine ⟨27109963326821459816028635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18073308884547639877352423 27109963326821459816028635)
      ·
        refine ⟨40664944990232189724042953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27109963326821459816028635 40664944990232189724042953)
        ·
          refine ⟨30498708742674142293032215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40664944990232189724042953 30498708742674142293032215)
          ·
            refine ⟨45748063114011213439548323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30498708742674142293032215 45748063114011213439548323)
            ·
              refine ⟨68622094671016820159322485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45748063114011213439548323 68622094671016820159322485)
              ·
                refine ⟨6433321375407826889936483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68622094671016820159322485 6433321375407826889936483)
                ·
                  refine ⟨9649982063111740334904725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433321375407826889936483 9649982063111740334904725)
                  ·
                    refine ⟨452342909208362828198659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9649982063111740334904725 452342909208362828198659)
                    ·
                      rfl

theorem cell22_1321402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_1321402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321402 prefixEnd_1321402 := by exact prefixLift 1321402
  have htrace : WordTrace (prefixWord ++ tailWord_1321402) baseStart_1321402 baseEnd_1321402 := by
    simpa [prefixWord, tailWord_1321402, baseEnd_1321402] using wordTrace_append hprefix tailTrace_1321402
  have hstable : (prefixWord ++ tailWord_1321402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321402).length < 2 ^ (prefixWord ++ tailWord_1321402).sum := by decide
  have hdescent : baseEnd_1321402 < baseStart_1321402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321404 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1321404 : Nat := 118140960795 + 1321404 * 2 ^ 59
def prefixEnd_1321404 : Nat := 4983230072969 + 3 ^ 40 * 1321404 * 2
def baseEnd_1321404 : Nat := 452343593849235489648653

theorem tailTrace_1321404 : CollatzResearch.WordTrace tailWord_1321404 prefixEnd_1321404 452343593849235489648653 := by
  unfold tailWord_1321404
  simp only [CollatzResearch.WordTrace]
  refine ⟨24097781652393230340589633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32130375536524307120786177 24097781652393230340589633)
  ·
    refine ⟨18073336239294922755442225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24097781652393230340589633 18073336239294922755442225)
    ·
      refine ⟨13555002179471192066581669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18073336239294922755442225 13555002179471192066581669)
      ·
        refine ⟨2541562908650848512484063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13555002179471192066581669 2541562908650848512484063)
        ·
          refine ⟨3812344362976272768726095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541562908650848512484063 3812344362976272768726095)
          ·
            refine ⟨5718516544464409153089143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812344362976272768726095 5718516544464409153089143)
            ·
              refine ⟨8577774816696613729633715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5718516544464409153089143 8577774816696613729633715)
              ·
                refine ⟨12866662225044920594450573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8577774816696613729633715 12866662225044920594450573)
                ·
                  refine ⟨4824998334391845222918965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12866662225044920594450573 4824998334391845222918965)
                  ·
                    refine ⟨452343593849235489648653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4824998334391845222918965 452343593849235489648653)
                    ·
                      rfl

theorem cell22_1321404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1321404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321404 prefixEnd_1321404 := by exact prefixLift 1321404
  have htrace : WordTrace (prefixWord ++ tailWord_1321404) baseStart_1321404 baseEnd_1321404 := by
    simpa [prefixWord, tailWord_1321404, baseEnd_1321404] using wordTrace_append hprefix tailTrace_1321404
  have hstable : (prefixWord ++ tailWord_1321404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321404).length < 2 ^ (prefixWord ++ tailWord_1321404).sum := by decide
  have hdescent : baseEnd_1321404 < baseStart_1321404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321432 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_1321432 : Nat := 118140960795 + 1321432 * 2 ^ 59
def prefixEnd_1321432 : Nat := 4983230072969 + 3 ^ 40 * 1321432 * 2
def baseEnd_1321432 : Nat := 452353178821452749948567

theorem tailTrace_1321432 : CollatzResearch.WordTrace tailWord_1321432 prefixEnd_1321432 452353178821452749948567 := by
  unfold tailWord_1321432
  simp only [CollatzResearch.WordTrace]
  refine ⟨24098292274342510731599275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32131056365790014308799033 24098292274342510731599275)
  ·
    refine ⟨36147438411513766097398913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24098292274342510731599275 36147438411513766097398913)
    ·
      refine ⟨27110578808635324573049185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36147438411513766097398913 27110578808635324573049185)
      ·
        refine ⟨20332934106476493429786889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27110578808635324573049185 20332934106476493429786889)
        ·
          refine ⟨15249700579857370072340167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20332934106476493429786889 15249700579857370072340167)
          ·
            refine ⟨22874550869786055108510251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15249700579857370072340167 22874550869786055108510251)
            ·
              refine ⟨34311826304679082662765377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22874550869786055108510251 34311826304679082662765377)
              ·
                refine ⟨25733869728509311997074033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34311826304679082662765377 25733869728509311997074033)
                ·
                  refine ⟨19300402296381983997805525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25733869728509311997074033 19300402296381983997805525)
                  ·
                    refine ⟨452353178821452749948567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19300402296381983997805525 452353178821452749948567)
                    ·
                      rfl

theorem cell22_1321432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_1321432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321432 prefixEnd_1321432 := by exact prefixLift 1321432
  have htrace : WordTrace (prefixWord ++ tailWord_1321432) baseStart_1321432 baseEnd_1321432 := by
    simpa [prefixWord, tailWord_1321432, baseEnd_1321432] using wordTrace_append hprefix tailTrace_1321432
  have hstable : (prefixWord ++ tailWord_1321432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321432).length < 2 ^ (prefixWord ++ tailWord_1321432).sum := by decide
  have hdescent : baseEnd_1321432 < baseStart_1321432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321453 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1321453 : Nat := 118140960795 + 1321453 * 2 ^ 59
def prefixEnd_1321453 : Nat := 4983230072969 + 3 ^ 40 * 1321453 * 2
def baseEnd_1321453 : Nat := 452360367550615695173503

theorem tailTrace_1321453 : CollatzResearch.WordTrace tailWord_1321453 prefixEnd_1321453 452360367550615695173503 := by
  unfold tailWord_1321453
  simp only [CollatzResearch.WordTrace]
  refine ⟨48197350481608942049713013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32131566987739294699808675 48197350481608942049713013)
  ·
    refine ⟨4518501607650838317160595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48197350481608942049713013 4518501607650838317160595)
    ·
      refine ⟨6777752411476257475740893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518501607650838317160595 6777752411476257475740893)
      ·
        refine ⟨2541657154303596553402835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6777752411476257475740893 2541657154303596553402835)
        ·
          refine ⟨3812485731455394830104253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541657154303596553402835 3812485731455394830104253)
          ·
            refine ⟨1429682149295773061289095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3812485731455394830104253 1429682149295773061289095)
            ·
              refine ⟨2144523223943659591933643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429682149295773061289095 2144523223943659591933643)
              ·
                refine ⟨3216784835915489387900465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144523223943659591933643 3216784835915489387900465)
                ·
                  refine ⟨2412588626936617040925349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3216784835915489387900465 2412588626936617040925349)
                  ·
                    refine ⟨452360367550615695173503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412588626936617040925349 452360367550615695173503)
                    ·
                      rfl

theorem cell22_1321453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1321453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321453 prefixEnd_1321453 := by exact prefixLift 1321453
  have htrace : WordTrace (prefixWord ++ tailWord_1321453) baseStart_1321453 baseEnd_1321453 := by
    simpa [prefixWord, tailWord_1321453, baseEnd_1321453] using wordTrace_append hprefix tailTrace_1321453
  have hstable : (prefixWord ++ tailWord_1321453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321453).length < 2 ^ (prefixWord ++ tailWord_1321453).sum := by decide
  have hdescent : baseEnd_1321453 < baseStart_1321453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321483 : List Nat := [1, 1, 1, 1, 7, 1, 2, 4, 1, 3]
def baseStart_1321483 : Nat := 118140960795 + 1321483 * 2 ^ 59
def prefixEnd_1321483 : Nat := 4983230072969 + 3 ^ 40 * 1321483 * 2
def baseEnd_1321483 : Nat := 452370637163705616923411

theorem tailTrace_1321483 : CollatzResearch.WordTrace tailWord_1321483 prefixEnd_1321483 452370637163705616923411 := by
  unfold tailWord_1321483
  simp only [CollatzResearch.WordTrace]
  refine ⟨48198444671500257173305103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32132296447666838115536735 48198444671500257173305103)
  ·
    refine ⟨72297667007250385759957655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48198444671500257173305103 72297667007250385759957655)
    ·
      refine ⟨108446500510875578639936483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72297667007250385759957655 108446500510875578639936483)
      ·
        refine ⟨162669750766313367959904725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108446500510875578639936483 162669750766313367959904725)
        ·
          refine ⟨3812572283585469561560267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 162669750766313367959904725 3812572283585469561560267)
          ·
            refine ⟨5718858425378204342340401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812572283585469561560267 5718858425378204342340401)
            ·
              refine ⟨4289143819033653256755301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5718858425378204342340401 4289143819033653256755301)
              ·
                refine ⟨804214466068809985641619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4289143819033653256755301 804214466068809985641619)
                ·
                  refine ⟨1206321699103214978462429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804214466068809985641619 1206321699103214978462429)
                  ·
                    refine ⟨452370637163705616923411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1206321699103214978462429 452370637163705616923411)
                    ·
                      rfl

theorem cell22_1321483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 3].length) (baseStart_1321483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321483 prefixEnd_1321483 := by exact prefixLift 1321483
  have htrace : WordTrace (prefixWord ++ tailWord_1321483) baseStart_1321483 baseEnd_1321483 := by
    simpa [prefixWord, tailWord_1321483, baseEnd_1321483] using wordTrace_append hprefix tailTrace_1321483
  have hstable : (prefixWord ++ tailWord_1321483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321483).length < 2 ^ (prefixWord ++ tailWord_1321483).sum := by decide
  have hdescent : baseEnd_1321483 < baseStart_1321483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321509 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_1321509 : Nat := 118140960795 + 1321509 * 2 ^ 59
def prefixEnd_1321509 : Nat := 4983230072969 + 3 ^ 40 * 1321509 * 2
def baseEnd_1321509 : Nat := 452379537495050215773331

theorem tailTrace_1321509 : CollatzResearch.WordTrace tailWord_1321509 prefixEnd_1321509 452379537495050215773331 := by
  unfold tailWord_1321509
  simp only [CollatzResearch.WordTrace]
  refine ⟨48199392969406063613751581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32132928646270709075834387 48199392969406063613751581)
  ·
    refine ⟨18074772363527273855156843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48199392969406063613751581 18074772363527273855156843)
    ·
      refine ⟨27112158545290910782735265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18074772363527273855156843 27112158545290910782735265)
      ·
        refine ⟨20334118908968183087051449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27112158545290910782735265 20334118908968183087051449)
        ·
          refine ⟨15250589181726137315288587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20334118908968183087051449 15250589181726137315288587)
          ·
            refine ⟨22875883772589205972932881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15250589181726137315288587 22875883772589205972932881)
            ·
              refine ⟨17156912829441904479699661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22875883772589205972932881 17156912829441904479699661)
              ·
                refine ⟨6433842311040714179887373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17156912829441904479699661 6433842311040714179887373)
                ·
                  refine ⟨2412690866640267817457765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6433842311040714179887373 2412690866640267817457765)
                  ·
                    refine ⟨452379537495050215773331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412690866640267817457765 452379537495050215773331)
                    ·
                      rfl

theorem cell22_1321509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_1321509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321509 prefixEnd_1321509 := by exact prefixLift 1321509
  have htrace : WordTrace (prefixWord ++ tailWord_1321509) baseStart_1321509 baseEnd_1321509 := by
    simpa [prefixWord, tailWord_1321509, baseEnd_1321509] using wordTrace_append hprefix tailTrace_1321509
  have hstable : (prefixWord ++ tailWord_1321509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321509).length < 2 ^ (prefixWord ++ tailWord_1321509).sum := by decide
  have hdescent : baseEnd_1321509 < baseStart_1321509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321534 : List Nat := [4, 2, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_1321534 : Nat := 118140960795 + 1321534 * 2 ^ 59
def prefixEnd_1321534 : Nat := 4983230072969 + 3 ^ 40 * 1321534 * 2
def baseEnd_1321534 : Nat := 452388095505958483898255

theorem tailTrace_1321534 : CollatzResearch.WordTrace tailWord_1321534 prefixEnd_1321534 452388095505958483898255 := by
  unfold tailWord_1321534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025038099289436610426457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32133536529543661922274437 6025038099289436610426457)
  ·
    refine ⟨4518778574467077457819843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6025038099289436610426457 4518778574467077457819843)
    ·
      refine ⟨6778167861700616186729765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518778574467077457819843 6778167861700616186729765)
      ·
        refine ⟨1270906474068865535011831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6778167861700616186729765 1270906474068865535011831)
        ·
          refine ⟨1906359711103298302517747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270906474068865535011831 1906359711103298302517747)
          ·
            refine ⟨2859539566654947453776621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906359711103298302517747 2859539566654947453776621)
            ·
              refine ⟨1072327337495605295166233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859539566654947453776621 1072327337495605295166233)
              ·
                refine ⟨804245503121703971374675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072327337495605295166233 804245503121703971374675)
                ·
                  refine ⟨1206368254682555957062013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804245503121703971374675 1206368254682555957062013)
                  ·
                    refine ⟨452388095505958483898255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1206368254682555957062013 452388095505958483898255)
                    ·
                      rfl

theorem cell22_1321534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_1321534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321534 prefixEnd_1321534 := by exact prefixLift 1321534
  have htrace : WordTrace (prefixWord ++ tailWord_1321534) baseStart_1321534 baseEnd_1321534 := by
    simpa [prefixWord, tailWord_1321534, baseEnd_1321534] using wordTrace_append hprefix tailTrace_1321534
  have hstable : (prefixWord ++ tailWord_1321534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321534).length < 2 ^ (prefixWord ++ tailWord_1321534).sum := by decide
  have hdescent : baseEnd_1321534 < baseStart_1321534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321541 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 6]
def baseStart_1321541 : Nat := 118140960795 + 1321541 * 2 ^ 59
def prefixEnd_1321541 : Nat := 4983230072969 + 3 ^ 40 * 1321541 * 2
def baseEnd_1321541 : Nat := 150796830583004266324411

theorem tailTrace_1321541 : CollatzResearch.WordTrace tailWord_1321541 prefixEnd_1321541 150796830583004266324411 := by
  unfold tailWord_1321541
  simp only [CollatzResearch.WordTrace]
  refine ⟨48200560105290133078916477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32133706736860088719277651 48200560105290133078916477)
  ·
    refine ⟨18075210039483799904593679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48200560105290133078916477 18075210039483799904593679)
    ·
      refine ⟨27112815059225699856890519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18075210039483799904593679 27112815059225699856890519)
      ·
        refine ⟨40669222588838549785335779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27112815059225699856890519 40669222588838549785335779)
        ·
          refine ⟨61003833883257824678003669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40669222588838549785335779 61003833883257824678003669)
          ·
            refine ⟨1429777356638855265890711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 61003833883257824678003669 1429777356638855265890711)
            ·
              refine ⟨2144666034958282898836067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429777356638855265890711 2144666034958282898836067)
              ·
                refine ⟨3216999052437424348254101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144666034958282898836067 3216999052437424348254101)
                ·
                  refine ⟨150796830583004266324411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3216999052437424348254101 150796830583004266324411)
                  ·
                    rfl

theorem cell22_1321541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_1321541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321541 prefixEnd_1321541 := by exact prefixLift 1321541
  have htrace : WordTrace (prefixWord ++ tailWord_1321541) baseStart_1321541 baseEnd_1321541 := by
    simpa [prefixWord, tailWord_1321541, baseEnd_1321541] using wordTrace_append hprefix tailTrace_1321541
  have hstable : (prefixWord ++ tailWord_1321541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321541).length < 2 ^ (prefixWord ++ tailWord_1321541).sum := by decide
  have hdescent : baseEnd_1321541 < baseStart_1321541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321569 : List Nat := [1, 2, 3, 1, 1, 4, 2, 8]
def baseStart_1321569 : Nat := 118140960795 + 1321569 * 2 ^ 59
def prefixEnd_1321569 : Nat := 4983230072969 + 3 ^ 40 * 1321569 * 2
def baseEnd_1321569 : Nat := 50266675191247784363683

theorem tailTrace_1321569 : CollatzResearch.WordTrace tailWord_1321569 prefixEnd_1321569 50266675191247784363683 := by
  unfold tailWord_1321569
  simp only [CollatzResearch.WordTrace]
  refine ⟨48201581349188693860935761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32134387566125795907290507 48201581349188693860935761)
  ·
    refine ⟨36151186011891520395701821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48201581349188693860935761 36151186011891520395701821)
    ·
      refine ⟨13556694754459320148388183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36151186011891520395701821 13556694754459320148388183)
      ·
        refine ⟨20335042131688980222582275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13556694754459320148388183 20335042131688980222582275)
        ·
          refine ⟨30502563197533470333873413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20335042131688980222582275 30502563197533470333873413)
          ·
            refine ⟨5719230599537525687601265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30502563197533470333873413 5719230599537525687601265)
            ·
              refine ⟨4289422949653144265700949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5719230599537525687601265 4289422949653144265700949)
              ·
                refine ⟨50266675191247784363683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4289422949653144265700949 50266675191247784363683)
                ·
                  rfl

theorem cell22_1321569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 8].length) (baseStart_1321569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321569 prefixEnd_1321569 := by exact prefixLift 1321569
  have htrace : WordTrace (prefixWord ++ tailWord_1321569) baseStart_1321569 baseEnd_1321569 := by
    simpa [prefixWord, tailWord_1321569, baseEnd_1321569] using wordTrace_append hprefix tailTrace_1321569
  have hstable : (prefixWord ++ tailWord_1321569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321569).length < 2 ^ (prefixWord ++ tailWord_1321569).sum := by decide
  have hdescent : baseEnd_1321569 < baseStart_1321569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321571 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 2, 4]
def baseStart_1321571 : Nat := 118140960795 + 1321571 * 2 ^ 59
def prefixEnd_1321571 : Nat := 4983230072969 + 3 ^ 40 * 1321571 * 2
def baseEnd_1321571 : Nat := 452400761362102720723141

theorem tailTrace_1321571 : CollatzResearch.WordTrace tailWord_1321571 prefixEnd_1321571 452400761362102720723141 := by
  unfold tailWord_1321571
  simp only [CollatzResearch.WordTrace]
  refine ⟨48201654295181448202508567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32134436196787632135005711 48201654295181448202508567)
  ·
    refine ⟨72302481442772172303762851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48201654295181448202508567 72302481442772172303762851)
    ·
      refine ⟨108453722164158258455644277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72302481442772172303762851 108453722164158258455644277)
      ·
        refine ⟨10167536452889836730216651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108453722164158258455644277 10167536452889836730216651)
        ·
          refine ⟨15251304679334755095324977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10167536452889836730216651 15251304679334755095324977)
          ·
            refine ⟨11438478509501066321493733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15251304679334755095324977 11438478509501066321493733)
            ·
              refine ⟨2144714720531449935280075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11438478509501066321493733 2144714720531449935280075)
              ·
                refine ⟨3217072080797174902920113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2144714720531449935280075 3217072080797174902920113)
                ·
                  refine ⟨2412804060597881177190085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3217072080797174902920113 2412804060597881177190085)
                  ·
                    refine ⟨452400761362102720723141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412804060597881177190085 452400761362102720723141)
                    ·
                      rfl

theorem cell22_1321571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 4].length) (baseStart_1321571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321571 prefixEnd_1321571 := by exact prefixLift 1321571
  have htrace : WordTrace (prefixWord ++ tailWord_1321571) baseStart_1321571 baseEnd_1321571 := by
    simpa [prefixWord, tailWord_1321571, baseEnd_1321571] using wordTrace_append hprefix tailTrace_1321571
  have hstable : (prefixWord ++ tailWord_1321571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321571).length < 2 ^ (prefixWord ++ tailWord_1321571).sum := by decide
  have hdescent : baseEnd_1321571 < baseStart_1321571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321586 : List Nat := [3, 2, 1, 2, 5, 9]
def baseStart_1321586 : Nat := 118140960795 + 1321586 * 2 ^ 59
def prefixEnd_1321586 : Nat := 4983230072969 + 3 ^ 40 * 1321586 * 2
def baseEnd_1321586 : Nat := 5585257977390712118495

theorem tailTrace_1321586 : CollatzResearch.WordTrace tailWord_1321586 prefixEnd_1321586 5585257977390712118495 := by
  unfold tailWord_1321586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12050550347531776441076153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32134800926751403842869741 12050550347531776441076153)
  ·
    refine ⟨9037912760648832330807115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12050550347531776441076153 9037912760648832330807115)
    ·
      refine ⟨13556869140973248496210673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9037912760648832330807115 13556869140973248496210673)
      ·
        refine ⟨10167651855729936372158005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13556869140973248496210673 10167651855729936372158005)
        ·
          refine ⟨953217361474681534889813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10167651855729936372158005 953217361474681534889813)
          ·
            refine ⟨5585257977390712118495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 953217361474681534889813 5585257977390712118495)
            ·
              rfl

theorem cell22_1321586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 9].length) (baseStart_1321586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321586 prefixEnd_1321586 := by exact prefixLift 1321586
  have htrace : WordTrace (prefixWord ++ tailWord_1321586) baseStart_1321586 baseEnd_1321586 := by
    simpa [prefixWord, tailWord_1321586, baseEnd_1321586] using wordTrace_append hprefix tailTrace_1321586
  have hstable : (prefixWord ++ tailWord_1321586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321586).length < 2 ^ (prefixWord ++ tailWord_1321586).sum := by decide
  have hdescent : baseEnd_1321586 < baseStart_1321586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321618 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1321618 : Nat := 118140960795 + 1321618 * 2 ^ 59
def prefixEnd_1321618 : Nat := 4983230072969 + 3 ^ 40 * 1321618 * 2
def baseEnd_1321618 : Nat := 452416850422610264797997

theorem tailTrace_1321618 : CollatzResearch.WordTrace tailWord_1321618 prefixEnd_1321618 452416850422610264797997 := by
  unfold tailWord_1321618
  simp only [CollatzResearch.WordTrace]
  refine ⟨12050842131502793807367377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32135579017340783486313005 12050842131502793807367377)
  ·
    refine ⟨9038131598627095355525533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12050842131502793807367377 9038131598627095355525533)
    ·
      refine ⟨3389299349485160758322075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9038131598627095355525533 3389299349485160758322075)
      ·
        refine ⟨5083949024227741137483113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389299349485160758322075 5083949024227741137483113)
        ·
          refine ⟨3812961768170805853112335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5083949024227741137483113 3812961768170805853112335)
          ·
            refine ⟨5719442652256208779668503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3812961768170805853112335 5719442652256208779668503)
            ·
              refine ⟨8579163978384313169502755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5719442652256208779668503 8579163978384313169502755)
              ·
                refine ⟨12868745967576469754254133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8579163978384313169502755 12868745967576469754254133)
                ·
                  refine ⟨1206444934460294039461325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12868745967576469754254133 1206444934460294039461325)
                  ·
                    refine ⟨452416850422610264797997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1206444934460294039461325 452416850422610264797997)
                    ·
                      rfl

theorem cell22_1321618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1321618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321618 prefixEnd_1321618 := by exact prefixLift 1321618
  have htrace : WordTrace (prefixWord ++ tailWord_1321618) baseStart_1321618 baseEnd_1321618 := by
    simpa [prefixWord, tailWord_1321618, baseEnd_1321618] using wordTrace_append hprefix tailTrace_1321618
  have hstable : (prefixWord ++ tailWord_1321618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321618).length < 2 ^ (prefixWord ++ tailWord_1321618).sum := by decide
  have hdescent : baseEnd_1321618 < baseStart_1321618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321678 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1321678 : Nat := 118140960795 + 1321678 * 2 ^ 59
def prefixEnd_1321678 : Nat := 4983230072969 + 3 ^ 40 * 1321678 * 2
def baseEnd_1321678 : Nat := 452437389648790108297813

theorem tailTrace_1321678 : CollatzResearch.WordTrace tailWord_1321678 prefixEnd_1321678 452437389648790108297813 := by
  unfold tailWord_1321678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025694613224225684581711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32137037937195870317769125 6025694613224225684581711)
  ·
    refine ⟨9038541919836338526872567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6025694613224225684581711 9038541919836338526872567)
    ·
      refine ⟨13557812879754507790308851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9038541919836338526872567 13557812879754507790308851)
      ·
        refine ⟨20336719319631761685463277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13557812879754507790308851 20336719319631761685463277)
        ·
          refine ⟨7626269744861910632048729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20336719319631761685463277 7626269744861910632048729)
          ·
            refine ⟨5719702308646432974036547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7626269744861910632048729 5719702308646432974036547)
            ·
              refine ⟨8579553462969649461054821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5719702308646432974036547 8579553462969649461054821)
              ·
                refine ⟨1608666274306809273947779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8579553462969649461054821 1608666274306809273947779)
                ·
                  refine ⟨2412999411460213910921669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608666274306809273947779 2412999411460213910921669)
                  ·
                    refine ⟨452437389648790108297813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412999411460213910921669 452437389648790108297813)
                    ·
                      rfl

theorem cell22_1321678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1321678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321678 prefixEnd_1321678 := by exact prefixLift 1321678
  have htrace : WordTrace (prefixWord ++ tailWord_1321678) baseStart_1321678 baseEnd_1321678 := by
    simpa [prefixWord, tailWord_1321678, baseEnd_1321678] using wordTrace_append hprefix tailTrace_1321678
  have hstable : (prefixWord ++ tailWord_1321678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321678).length < 2 ^ (prefixWord ++ tailWord_1321678).sum := by decide
  have hdescent : baseEnd_1321678 < baseStart_1321678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321708 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_1321708 : Nat := 118140960795 + 1321708 * 2 ^ 59
def prefixEnd_1321708 : Nat := 4983230072969 + 3 ^ 40 * 1321708 * 2
def baseEnd_1321708 : Nat := 452447659261880030047721

theorem tailTrace_1321708 : CollatzResearch.WordTrace tailWord_1321708 prefixEnd_1321708 452447659261880030047721 := by
  unfold tailWord_1321708
  simp only [CollatzResearch.WordTrace]
  refine ⟨24103325547842560300122889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32137767397123413733497185 24103325547842560300122889)
  ·
    refine ⟨18077494160881920225092167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24103325547842560300122889 18077494160881920225092167)
    ·
      refine ⟨27116241241322880337638251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18077494160881920225092167 27116241241322880337638251)
      ·
        refine ⟨40674361861984320506457377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27116241241322880337638251 40674361861984320506457377)
        ·
          refine ⟨30505771396488240379843033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40674361861984320506457377 30505771396488240379843033)
          ·
            refine ⟨22879328547366180284882275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30505771396488240379843033 22879328547366180284882275)
            ·
              refine ⟨34318992821049270427323413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22879328547366180284882275 34318992821049270427323413)
              ·
                refine ⟨1608702788486684551280785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34318992821049270427323413 1608702788486684551280785)
                ·
                  refine ⟨1206527091365013413460589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1608702788486684551280785 1206527091365013413460589)
                  ·
                    refine ⟨452447659261880030047721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1206527091365013413460589 452447659261880030047721)
                    ·
                      rfl

theorem cell22_1321708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_1321708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321708 prefixEnd_1321708 := by exact prefixLift 1321708
  have htrace : WordTrace (prefixWord ++ tailWord_1321708) baseStart_1321708 baseEnd_1321708 := by
    simpa [prefixWord, tailWord_1321708, baseEnd_1321708] using wordTrace_append hprefix tailTrace_1321708
  have hstable : (prefixWord ++ tailWord_1321708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321708).length < 2 ^ (prefixWord ++ tailWord_1321708).sum := by decide
  have hdescent : baseEnd_1321708 < baseStart_1321708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321716 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1321716 : Nat := 118140960795 + 1321716 * 2 ^ 59
def prefixEnd_1321716 : Nat := 4983230072969 + 3 ^ 40 * 1321716 * 2
def baseEnd_1321716 : Nat := 150816799275123558615899

theorem tailTrace_1321716 : CollatzResearch.WordTrace tailWord_1321716 prefixEnd_1321716 150816799275123558615899 := by
  unfold tailWord_1321716
  simp only [CollatzResearch.WordTrace]
  refine ⟨24103471439828068983268501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32137961919770758644358001 24103471439828068983268501)
  ·
    refine ⟨1129850223741940733590711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24103471439828068983268501 1129850223741940733590711)
    ·
      refine ⟨1694775335612911100386067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1129850223741940733590711 1694775335612911100386067)
      ·
        refine ⟨2542163003419366650579101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1694775335612911100386067 2542163003419366650579101)
        ·
          refine ⟨953311126282262493967163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2542163003419366650579101 953311126282262493967163)
          ·
            refine ⟨1429966689423393740950745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953311126282262493967163 1429966689423393740950745)
            ·
              refine ⟨1072475017067545305713059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429966689423393740950745 1072475017067545305713059)
              ·
                refine ⟨1608712525601317958569589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072475017067545305713059 1608712525601317958569589)
                ·
                  refine ⟨150816799275123558615899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1608712525601317958569589 150816799275123558615899)
                  ·
                    rfl

theorem cell22_1321716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1321716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321716 prefixEnd_1321716 := by exact prefixLift 1321716
  have htrace : WordTrace (prefixWord ++ tailWord_1321716) baseStart_1321716 baseEnd_1321716 := by
    simpa [prefixWord, tailWord_1321716, baseEnd_1321716] using wordTrace_append hprefix tailTrace_1321716
  have hstable : (prefixWord ++ tailWord_1321716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321716).length < 2 ^ (prefixWord ++ tailWord_1321716).sum := by decide
  have hdescent : baseEnd_1321716 < baseStart_1321716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321828 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1321828 : Nat := 118140960795 + 1321828 * 2 ^ 59
def prefixEnd_1321828 : Nat := 4983230072969 + 3 ^ 40 * 1321828 * 2
def baseEnd_1321828 : Nat := 150829579238079905682451

theorem tailTrace_1321828 : CollatzResearch.WordTrace tailWord_1321828 prefixEnd_1321828 150829579238079905682451 := by
  unfold tailWord_1321828
  simp only [CollatzResearch.WordTrace]
  refine ⟨24105513927625190547307069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32140685236833587396409425 24105513927625190547307069)
  ·
    refine ⟨9039567722859446455240151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24105513927625190547307069 9039567722859446455240151)
    ·
      refine ⟨13559351584289169682860227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9039567722859446455240151 13559351584289169682860227)
      ·
        refine ⟨20339027376433754524290341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13559351584289169682860227 20339027376433754524290341)
        ·
          refine ⟨3813567633081328973304439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20339027376433754524290341 3813567633081328973304439)
          ·
            refine ⟨5720351449621993459956659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3813567633081328973304439 5720351449621993459956659)
            ·
              refine ⟨8580527174432990189934989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5720351449621993459956659 8580527174432990189934989)
              ·
                refine ⟨3217697690412371321225621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8580527174432990189934989 3217697690412371321225621)
                ·
                  refine ⟨150829579238079905682451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3217697690412371321225621 150829579238079905682451)
                  ·
                    rfl

theorem cell22_1321828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1321828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321828 prefixEnd_1321828 := by exact prefixLift 1321828
  have htrace : WordTrace (prefixWord ++ tailWord_1321828) baseStart_1321828 baseEnd_1321828 := by
    simpa [prefixWord, tailWord_1321828, baseEnd_1321828] using wordTrace_append hprefix tailTrace_1321828
  have hstable : (prefixWord ++ tailWord_1321828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321828).length < 2 ^ (prefixWord ++ tailWord_1321828).sum := by decide
  have hdescent : baseEnd_1321828 < baseStart_1321828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321843 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 1, 5]
def baseStart_1321843 : Nat := 118140960795 + 1321843 * 2 ^ 59
def prefixEnd_1321843 : Nat := 4983230072969 + 3 ^ 40 * 1321843 * 2
def baseEnd_1321843 : Nat := 452493872520784677922307

theorem tailTrace_1321843 : CollatzResearch.WordTrace tailWord_1321843 prefixEnd_1321843 452493872520784677922307 := by
  unfold tailWord_1321843
  simp only [CollatzResearch.WordTrace]
  refine ⟨48211574950196038656410183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32141049966797359104273455 48211574950196038656410183)
  ·
    refine ⟨72317362425294057984615275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48211574950196038656410183 72317362425294057984615275)
    ·
      refine ⟨108476043637941086976922913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72317362425294057984615275 108476043637941086976922913)
      ·
        refine ⟨81357032728455815232692185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108476043637941086976922913 81357032728455815232692185)
        ·
          refine ⟨61017774546341861424519139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81357032728455815232692185 61017774546341861424519139)
          ·
            refine ⟨91526661819512792136778709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61017774546341861424519139 91526661819512792136778709)
            ·
              refine ⟨2145156136394831065705751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 91526661819512792136778709 2145156136394831065705751)
              ·
                refine ⟨3217734204592246598558627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145156136394831065705751 3217734204592246598558627)
                ·
                  refine ⟨4826601306888369897837941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217734204592246598558627 4826601306888369897837941)
                  ·
                    refine ⟨452493872520784677922307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4826601306888369897837941 452493872520784677922307)
                    ·
                      rfl

theorem cell22_1321843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 5].length) (baseStart_1321843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321843 prefixEnd_1321843 := by exact prefixLift 1321843
  have htrace : WordTrace (prefixWord ++ tailWord_1321843) baseStart_1321843 baseEnd_1321843 := by
    simpa [prefixWord, tailWord_1321843, baseEnd_1321843] using wordTrace_append hprefix tailTrace_1321843
  have hstable : (prefixWord ++ tailWord_1321843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321843).length < 2 ^ (prefixWord ++ tailWord_1321843).sum := by decide
  have hdescent : baseEnd_1321843 < baseStart_1321843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321890 : List Nat := [3, 3, 1, 2, 2, 2, 2, 7]
def baseStart_1321890 : Nat := 118140960795 + 1321890 * 2 ^ 59
def prefixEnd_1321890 : Nat := 4983230072969 + 3 ^ 40 * 1321890 * 2
def baseEnd_1321890 : Nat := 50278884620143580221907

theorem tailTrace_1321890 : CollatzResearch.WordTrace tailWord_1321890 prefixEnd_1321890 50278884620143580221907 := by
  unfold tailWord_1321890
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053322295256441420842781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32142192787350510455580749 12053322295256441420842781)
  ·
    refine ⟨4519995860721165532816043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12053322295256441420842781 4519995860721165532816043)
    ·
      refine ⟨6779993791081748299224065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4519995860721165532816043 6779993791081748299224065)
      ·
        refine ⟨5084995343311311224418049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6779993791081748299224065 5084995343311311224418049)
        ·
          refine ⟨3813746507483483418313537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5084995343311311224418049 3813746507483483418313537)
          ·
            refine ⟨2860309880612612563735153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813746507483483418313537 2860309880612612563735153)
            ·
              refine ⟨2145232410459459422801365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860309880612612563735153 2145232410459459422801365)
              ·
                refine ⟨50278884620143580221907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2145232410459459422801365 50278884620143580221907)
                ·
                  rfl

theorem cell22_1321890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_1321890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321890 prefixEnd_1321890 := by exact prefixLift 1321890
  have htrace : WordTrace (prefixWord ++ tailWord_1321890) baseStart_1321890 baseEnd_1321890 := by
    simpa [prefixWord, tailWord_1321890, baseEnd_1321890] using wordTrace_append hprefix tailTrace_1321890
  have hstable : (prefixWord ++ tailWord_1321890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321890).length < 2 ^ (prefixWord ++ tailWord_1321890).sum := by decide
  have hdescent : baseEnd_1321890 < baseStart_1321890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321935 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 5]
def baseStart_1321935 : Nat := 118140960795 + 1321935 * 2 ^ 59
def prefixEnd_1321935 : Nat := 4983230072969 + 3 ^ 40 * 1321935 * 2
def baseEnd_1321935 : Nat := 150841788666975701540675

theorem tailTrace_1321935 : CollatzResearch.WordTrace tailWord_1321935 prefixEnd_1321935 150841788666975701540675 := by
  unfold tailWord_1321935
  simp only [CollatzResearch.WordTrace]
  refine ⟨48214930465862738368759259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32143286977241825579172839 48214930465862738368759259)
  ·
    refine ⟨72322395698794107553138889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48214930465862738368759259 72322395698794107553138889)
    ·
      refine ⟨54241796774095580664854167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72322395698794107553138889 54241796774095580664854167)
      ·
        refine ⟨81362695161143370997281251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54241796774095580664854167 81362695161143370997281251)
        ·
          refine ⟨122044042741715056495921877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81362695161143370997281251 122044042741715056495921877)
          ·
            refine ⟨2860407251758946636623169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 122044042741715056495921877 2860407251758946636623169)
            ·
              refine ⟨2145305438819209977467377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860407251758946636623169 2145305438819209977467377)
              ·
                refine ⟨1608979079114407483100533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2145305438819209977467377 1608979079114407483100533)
                ·
                  refine ⟨150841788666975701540675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1608979079114407483100533 150841788666975701540675)
                  ·
                    rfl

theorem cell22_1321935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 5].length) (baseStart_1321935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321935 prefixEnd_1321935 := by exact prefixLift 1321935
  have htrace : WordTrace (prefixWord ++ tailWord_1321935) baseStart_1321935 baseEnd_1321935 := by
    simpa [prefixWord, tailWord_1321935, baseEnd_1321935] using wordTrace_append hprefix tailTrace_1321935
  have hstable : (prefixWord ++ tailWord_1321935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321935).length < 2 ^ (prefixWord ++ tailWord_1321935).sum := by decide
  have hdescent : baseEnd_1321935 < baseStart_1321935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321973 : List Nat := [1, 3, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1321973 : Nat := 118140960795 + 1321973 * 2 ^ 59
def prefixEnd_1321973 : Nat := 4983230072969 + 3 ^ 40 * 1321973 * 2
def baseEnd_1321973 : Nat := 452538374177507672171909

theorem tailTrace_1321973 : CollatzResearch.WordTrace tailWord_1321973 prefixEnd_1321973 452538374177507672171909 := by
  unfold tailWord_1321973
  simp only [CollatzResearch.WordTrace]
  refine ⟨48216316439725070858642573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32144210959816713905761715 48216316439725070858642573)
  ·
    refine ⟨18081118664896901571990965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48216316439725070858642573 18081118664896901571990965)
    ·
      refine ⟨1695104874834084522374153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18081118664896901571990965 1695104874834084522374153)
      ·
        refine ⟨1271328656125563391780615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695104874834084522374153 1271328656125563391780615)
        ·
          refine ⟨1906992984188345087670923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271328656125563391780615 1906992984188345087670923)
          ·
            refine ⟨2860489476282517631506385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906992984188345087670923 2860489476282517631506385)
            ·
              refine ⟨2145367107211888223629789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860489476282517631506385 2145367107211888223629789)
              ·
                refine ⟨804512665204458083861171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2145367107211888223629789 804512665204458083861171)
                ·
                  refine ⟨1206768997806687125791757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804512665204458083861171 1206768997806687125791757)
                  ·
                    refine ⟨452538374177507672171909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1206768997806687125791757 452538374177507672171909)
                    ·
                      rfl

theorem cell22_1321973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1321973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321973 prefixEnd_1321973 := by exact prefixLift 1321973
  have htrace : WordTrace (prefixWord ++ tailWord_1321973) baseStart_1321973 baseEnd_1321973 := by
    simpa [prefixWord, tailWord_1321973, baseEnd_1321973] using wordTrace_append hprefix tailTrace_1321973
  have hstable : (prefixWord ++ tailWord_1321973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321973).length < 2 ^ (prefixWord ++ tailWord_1321973).sum := by decide
  have hdescent : baseEnd_1321973 < baseStart_1321973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1321986 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1321986 : Nat := 118140960795 + 1321986 * 2 ^ 59
def prefixEnd_1321986 : Nat := 4983230072969 + 3 ^ 40 * 1321986 * 2
def baseEnd_1321986 : Nat := 150847608114393323865623

theorem tailTrace_1321986 : CollatzResearch.WordTrace tailWord_1321986 prefixEnd_1321986 150847608114393323865623 := by
  unfold tailWord_1321986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054197647169493519716453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32144527059118649385910541 12054197647169493519716453)
  ·
    refine ⟨2260162058844280034946835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12054197647169493519716453 2260162058844280034946835)
    ·
      refine ⟨3390243088266420052420253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260162058844280034946835 3390243088266420052420253)
      ·
        refine ⟨1271341158099907519657595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3390243088266420052420253 1271341158099907519657595)
        ·
          refine ⟨1907011737149861279486393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271341158099907519657595 1907011737149861279486393)
          ·
            refine ⟨1430258802862395959614795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1907011737149861279486393 1430258802862395959614795)
            ·
              refine ⟨2145388204293593939422193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430258802862395959614795 2145388204293593939422193)
              ·
                refine ⟨1609041153220195454566645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2145388204293593939422193 1609041153220195454566645)
                ·
                  refine ⟨150847608114393323865623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1609041153220195454566645 150847608114393323865623)
                  ·
                    rfl

theorem cell22_1321986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1321986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1321986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1321986 prefixEnd_1321986 := by exact prefixLift 1321986
  have htrace : WordTrace (prefixWord ++ tailWord_1321986) baseStart_1321986 baseEnd_1321986 := by
    simpa [prefixWord, tailWord_1321986, baseEnd_1321986] using wordTrace_append hprefix tailTrace_1321986
  have hstable : (prefixWord ++ tailWord_1321986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1321986).length < 2 ^ (prefixWord ++ tailWord_1321986).sum := by decide
  have hdescent : baseEnd_1321986 < baseStart_1321986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1321986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322102 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1322102 : Nat := 118140960795 + 1322102 * 2 ^ 59
def prefixEnd_1322102 : Nat := 4983230072969 + 3 ^ 40 * 1322102 * 2
def baseEnd_1322102 : Nat := 452582533513794335696513

theorem tailTrace_1322102 : CollatzResearch.WordTrace tailWord_1322102 prefixEnd_1322102 452582533513794335696513 := by
  unfold tailWord_1322102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013813841016107868130535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32147347637505150593392373 3013813841016107868130535)
  ·
    refine ⟨4520720761524161802195803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3013813841016107868130535 4520720761524161802195803)
    ·
      refine ⟨6781081142286242703293705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4520720761524161802195803 6781081142286242703293705)
      ·
        refine ⟨5085810856714682027470279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6781081142286242703293705 5085810856714682027470279)
        ·
          refine ⟨7628716285072023041205419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5085810856714682027470279 7628716285072023041205419)
          ·
            refine ⟨11443074427608034561808129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7628716285072023041205419 11443074427608034561808129)
            ·
              refine ⟨8582305820706025921356097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11443074427608034561808129 8582305820706025921356097)
              ·
                refine ⟨6436729365529519441017073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8582305820706025921356097 6436729365529519441017073)
                ·
                  refine ⟨4827547024147139580762805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6436729365529519441017073 4827547024147139580762805)
                  ·
                    refine ⟨452582533513794335696513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4827547024147139580762805 452582533513794335696513)
                    ·
                      rfl

theorem cell22_1322102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1322102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322102 prefixEnd_1322102 := by exact prefixLift 1322102
  have htrace : WordTrace (prefixWord ++ tailWord_1322102) baseStart_1322102 baseEnd_1322102 := by
    simpa [prefixWord, tailWord_1322102, baseEnd_1322102] using wordTrace_append hprefix tailTrace_1322102
  have hstable : (prefixWord ++ tailWord_1322102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322102).length < 2 ^ (prefixWord ++ tailWord_1322102).sum := by decide
  have hdescent : baseEnd_1322102 < baseStart_1322102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322115 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 6]
def baseStart_1322115 : Nat := 118140960795 + 1322115 * 2 ^ 59
def prefixEnd_1322115 : Nat := 4983230072969 + 3 ^ 40 * 1322115 * 2
def baseEnd_1322115 : Nat := 150862327893155545040491

theorem tailTrace_1322115 : CollatzResearch.WordTrace tailWord_1322115 prefixEnd_1322115 150862327893155545040491 := by
  unfold tailWord_1322115
  simp only [CollatzResearch.WordTrace]
  refine ⟨48221495605210629110311799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32147663736807086073541199 48221495605210629110311799)
  ·
    refine ⟨72332243407815943665467699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48221495605210629110311799 72332243407815943665467699)
    ·
      refine ⟨108498365111723915498201549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72332243407815943665467699 108498365111723915498201549)
      ·
        refine ⟨40686886916896468311825581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108498365111723915498201549 40686886916896468311825581)
        ·
          refine ⟨15257582593836175616934593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40686886916896468311825581 15257582593836175616934593)
          ·
            refine ⟨11443186945377131712700945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15257582593836175616934593 11443186945377131712700945)
            ·
              refine ⟨8582390209032848784525709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11443186945377131712700945 8582390209032848784525709)
              ·
                refine ⟨3218396328387318294197141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8582390209032848784525709 3218396328387318294197141)
                ·
                  refine ⟨150862327893155545040491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3218396328387318294197141 150862327893155545040491)
                  ·
                    rfl

theorem cell22_1322115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 6].length) (baseStart_1322115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322115 prefixEnd_1322115 := by exact prefixLift 1322115
  have htrace : WordTrace (prefixWord ++ tailWord_1322115) baseStart_1322115 baseEnd_1322115 := by
    simpa [prefixWord, tailWord_1322115, baseEnd_1322115] using wordTrace_append hprefix tailTrace_1322115
  have hstable : (prefixWord ++ tailWord_1322115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322115).length < 2 ^ (prefixWord ++ tailWord_1322115).sum := by decide
  have hdescent : baseEnd_1322115 < baseStart_1322115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322149 : List Nat := [1, 3, 1, 2, 1, 5, 2, 3, 4]
def baseStart_1322149 : Nat := 118140960795 + 1322149 * 2 ^ 59
def prefixEnd_1322149 : Nat := 4983230072969 + 3 ^ 40 * 1322149 * 2
def baseEnd_1322149 : Nat := 150866207524767293257123

theorem tailTrace_1322149 : CollatzResearch.WordTrace tailWord_1322149 prefixEnd_1322149 150866207524767293257123 := by
  unfold tailWord_1322149
  simp only [CollatzResearch.WordTrace]
  refine ⟨48222735687087452917049501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32148490458058301944699667 48222735687087452917049501)
  ·
    refine ⟨18083525882657794843893563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48222735687087452917049501 18083525882657794843893563)
    ·
      refine ⟨27125288823986692265840345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18083525882657794843893563 27125288823986692265840345)
      ·
        refine ⟨20343966617990019199380259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27125288823986692265840345 20343966617990019199380259)
        ·
          refine ⟨30515949926985028799070389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20343966617990019199380259 30515949926985028799070389)
          ·
            refine ⟨2860870305654846449912849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30515949926985028799070389 2860870305654846449912849)
            ·
              refine ⟨2145652729241134837434637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860870305654846449912849 2145652729241134837434637)
              ·
                refine ⟨804619773465425564037989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2145652729241134837434637 804619773465425564037989)
                ·
                  refine ⟨150866207524767293257123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 804619773465425564037989 150866207524767293257123)
                  ·
                    rfl

theorem cell22_1322149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_1322149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322149 prefixEnd_1322149 := by exact prefixLift 1322149
  have htrace : WordTrace (prefixWord ++ tailWord_1322149) baseStart_1322149 baseEnd_1322149 := by
    simpa [prefixWord, tailWord_1322149, baseEnd_1322149] using wordTrace_append hprefix tailTrace_1322149
  have hstable : (prefixWord ++ tailWord_1322149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322149).length < 2 ^ (prefixWord ++ tailWord_1322149).sum := by decide
  have hdescent : baseEnd_1322149 < baseStart_1322149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322151 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1322151 : Nat := 118140960795 + 1322151 * 2 ^ 59
def prefixEnd_1322151 : Nat := 4983230072969 + 3 ^ 40 * 1322151 * 2
def baseEnd_1322151 : Nat := 452599307215174541221363

theorem tailTrace_1322151 : CollatzResearch.WordTrace tailWord_1322151 prefixEnd_1322151 452599307215174541221363 := by
  unfold tailWord_1322151
  simp only [CollatzResearch.WordTrace]
  refine ⟨48222808633080207258622307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32148539088720138172414871 48222808633080207258622307)
  ·
    refine ⟨72334212949620310887933461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48222808633080207258622307 72334212949620310887933461)
    ·
      refine ⟨3390666232013452072871881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72334212949620310887933461 3390666232013452072871881)
      ·
        refine ⟨2542999674010089054653911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3390666232013452072871881 2542999674010089054653911)
        ·
          refine ⟨3814499511015133581980867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542999674010089054653911 3814499511015133581980867)
          ·
            refine ⟨5721749266522700372971301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3814499511015133581980867 5721749266522700372971301)
            ·
              refine ⟨1072827987473006319932119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5721749266522700372971301 1072827987473006319932119)
              ·
                refine ⟨1609241981209509479898179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072827987473006319932119 1609241981209509479898179)
                ·
                  refine ⟨2413862971814264219847269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609241981209509479898179 2413862971814264219847269)
                  ·
                    refine ⟨452599307215174541221363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2413862971814264219847269 452599307215174541221363)
                    ·
                      rfl

theorem cell22_1322151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1322151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322151 prefixEnd_1322151 := by exact prefixLift 1322151
  have htrace : WordTrace (prefixWord ++ tailWord_1322151) baseStart_1322151 baseEnd_1322151 := by
    simpa [prefixWord, tailWord_1322151, baseEnd_1322151] using wordTrace_append hprefix tailTrace_1322151
  have hstable : (prefixWord ++ tailWord_1322151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322151).length < 2 ^ (prefixWord ++ tailWord_1322151).sum := by decide
  have hdescent : baseEnd_1322151 < baseStart_1322151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322222 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_1322222 : Nat := 118140960795 + 1322222 * 2 ^ 59
def prefixEnd_1322222 : Nat := 4983230072969 + 3 ^ 40 * 1322222 * 2
def baseEnd_1322222 : Nat := 150874537322051340898715

theorem tailTrace_1322222 : CollatzResearch.WordTrace tailWord_1322222 prefixEnd_1322222 150874537322051340898715 := by
  unfold tailWord_1322222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028174776977873298057115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32150265477215324256304613 6028174776977873298057115)
  ·
    refine ⟨9042262165466809947085673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6028174776977873298057115 9042262165466809947085673)
    ·
      refine ⟨6781696624100107460314255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9042262165466809947085673 6781696624100107460314255)
      ·
        refine ⟨10172544936150161190471383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6781696624100107460314255 10172544936150161190471383)
        ·
          refine ⟨15258817404225241785707075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10172544936150161190471383 15258817404225241785707075)
          ·
            refine ⟨22888226106337862678560613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15258817404225241785707075 22888226106337862678560613)
            ·
              refine ⟨4291542394938349252230115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22888226106337862678560613 4291542394938349252230115)
              ·
                refine ⟨6437313592407523878345173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4291542394938349252230115 6437313592407523878345173)
                ·
                  refine ⟨150874537322051340898715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6437313592407523878345173 150874537322051340898715)
                  ·
                    rfl

theorem cell22_1322222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_1322222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322222 prefixEnd_1322222 := by exact prefixLift 1322222
  have htrace : WordTrace (prefixWord ++ tailWord_1322222) baseStart_1322222 baseEnd_1322222 := by
    simpa [prefixWord, tailWord_1322222, baseEnd_1322222] using wordTrace_append hprefix tailTrace_1322222
  have hstable : (prefixWord ++ tailWord_1322222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322222).length < 2 ^ (prefixWord ++ tailWord_1322222).sum := by decide
  have hdescent : baseEnd_1322222 < baseStart_1322222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322228 : List Nat := [2, 6, 1, 2, 1, 1, 2, 7]
def baseStart_1322228 : Nat := 118140960795 + 1322228 * 2 ^ 59
def prefixEnd_1322228 : Nat := 4983230072969 + 3 ^ 40 * 1322228 * 2
def baseEnd_1322228 : Nat := 50291740654308000782903

theorem tailTrace_1322228 : CollatzResearch.WordTrace tailWord_1322228 prefixEnd_1322228 50291740654308000782903 := by
  unfold tailWord_1322228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24112808526900624704587669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32150411369200832939450225 24112808526900624704587669)
  ·
    refine ⟨1130287899698466783027547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24112808526900624704587669 1130287899698466783027547)
    ·
      refine ⟨1695431849547700174541321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130287899698466783027547 1695431849547700174541321)
      ·
        refine ⟨1271573887160775130905991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695431849547700174541321 1271573887160775130905991)
        ·
          refine ⟨1907360830741162696358987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271573887160775130905991 1907360830741162696358987)
          ·
            refine ⟨2861041246111744044538481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907360830741162696358987 2861041246111744044538481)
            ·
              refine ⟨2145780934583808033403861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861041246111744044538481 2145780934583808033403861)
              ·
                refine ⟨50291740654308000782903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2145780934583808033403861 50291740654308000782903)
                ·
                  rfl

theorem cell22_1322228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 7].length) (baseStart_1322228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322228 prefixEnd_1322228 := by exact prefixLift 1322228
  have htrace : WordTrace (prefixWord ++ tailWord_1322228) baseStart_1322228 baseEnd_1322228 := by
    simpa [prefixWord, tailWord_1322228, baseEnd_1322228] using wordTrace_append hprefix tailTrace_1322228
  have hstable : (prefixWord ++ tailWord_1322228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322228).length < 2 ^ (prefixWord ++ tailWord_1322228).sum := by decide
  have hdescent : baseEnd_1322228 < baseStart_1322228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322239 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 5]
def baseStart_1322239 : Nat := 118140960795 + 1322239 * 2 ^ 59
def prefixEnd_1322239 : Nat := 4983230072969 + 3 ^ 40 * 1322239 * 2
def baseEnd_1322239 : Nat := 150876477137857215007031

theorem tailTrace_1322239 : CollatzResearch.WordTrace tailWord_1322239 prefixEnd_1322239 150876477137857215007031 := by
  unfold tailWord_1322239
  simp only [CollatzResearch.WordTrace]
  refine ⟨48226018256761398287825771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32150678837840932191883847 48226018256761398287825771)
  ·
    refine ⟨72339027385142097431738657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48226018256761398287825771 72339027385142097431738657)
    ·
      refine ⟨54254270538856573073803993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72339027385142097431738657 54254270538856573073803993)
      ·
        refine ⟨40690702904142429805352995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54254270538856573073803993 40690702904142429805352995)
        ·
          refine ⟨61036054356213644708029493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40690702904142429805352995 61036054356213644708029493)
          ·
            refine ⟨5722130095895029191377765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61036054356213644708029493 5722130095895029191377765)
            ·
              refine ⟨1072899392980317973383331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5722130095895029191377765 1072899392980317973383331)
              ·
                refine ⟨1609349089470476960074997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072899392980317973383331 1609349089470476960074997)
                ·
                  refine ⟨150876477137857215007031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1609349089470476960074997 150876477137857215007031)
                  ·
                    rfl

theorem cell22_1322239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 5].length) (baseStart_1322239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322239 prefixEnd_1322239 := by exact prefixLift 1322239
  have htrace : WordTrace (prefixWord ++ tailWord_1322239) baseStart_1322239 baseEnd_1322239 := by
    simpa [prefixWord, tailWord_1322239, baseEnd_1322239] using wordTrace_append hprefix tailTrace_1322239
  have hstable : (prefixWord ++ tailWord_1322239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322239).length < 2 ^ (prefixWord ++ tailWord_1322239).sum := by decide
  have hdescent : baseEnd_1322239 < baseStart_1322239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322301 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 6]
def baseStart_1322301 : Nat := 118140960795 + 1322301 * 2 ^ 59
def prefixEnd_1322301 : Nat := 4983230072969 + 3 ^ 40 * 1322301 * 2
def baseEnd_1322301 : Nat := 150883551760208049990301

theorem tailTrace_1322301 : CollatzResearch.WordTrace tailWord_1322301 prefixEnd_1322301 150883551760208049990301 := by
  unfold tailWord_1322301
  simp only [CollatzResearch.WordTrace]
  refine ⟨48228279582536782876582757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32152186388357855251055171 48228279582536782876582757)
  ·
    refine ⟨9042802421725646789359267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48228279582536782876582757 9042802421725646789359267)
    ·
      refine ⟨13564203632588470184038901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9042802421725646789359267 13564203632588470184038901)
      ·
        refine ⟨1271644090555169079753647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13564203632588470184038901 1271644090555169079753647)
        ·
          refine ⟨1907466135832753619630471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271644090555169079753647 1907466135832753619630471)
          ·
            refine ⟨2861199203749130429445707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907466135832753619630471 2861199203749130429445707)
            ·
              refine ⟨4291798805623695644168561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861199203749130429445707 4291798805623695644168561)
              ·
                refine ⟨3218849104217771733126421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4291798805623695644168561 3218849104217771733126421)
                ·
                  refine ⟨150883551760208049990301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3218849104217771733126421 150883551760208049990301)
                  ·
                    rfl

theorem cell22_1322301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_1322301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322301 prefixEnd_1322301 := by exact prefixLift 1322301
  have htrace : WordTrace (prefixWord ++ tailWord_1322301) baseStart_1322301 baseEnd_1322301 := by
    simpa [prefixWord, tailWord_1322301, baseEnd_1322301] using wordTrace_append hprefix tailTrace_1322301
  have hstable : (prefixWord ++ tailWord_1322301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322301).length < 2 ^ (prefixWord ++ tailWord_1322301).sum := by decide
  have hdescent : baseEnd_1322301 < baseStart_1322301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322350 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1322350 : Nat := 118140960795 + 1322350 * 2 ^ 59
def prefixEnd_1322350 : Nat := 4983230072969 + 3 ^ 40 * 1322350 * 2
def baseEnd_1322350 : Nat := 452667428982004355495753

theorem tailTrace_1322350 : CollatzResearch.WordTrace tailWord_1322350 prefixEnd_1322350 452667428982004355495753 := by
  unfold tailWord_1322350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028758344919908030639563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32153377839572842830077669 6028758344919908030639563)
  ·
    refine ⟨9043137517379862045959345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6028758344919908030639563 9043137517379862045959345)
    ·
      refine ⟨6782353138034896534469509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9043137517379862045959345 6782353138034896534469509)
      ·
        refine ⟨1271691213381543100213033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6782353138034896534469509 1271691213381543100213033)
        ·
          refine ⟨953768410036157325159775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1271691213381543100213033 953768410036157325159775)
          ·
            refine ⟨1430652615054235987739663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953768410036157325159775 1430652615054235987739663)
            ·
              refine ⟨2145978922581353981609495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430652615054235987739663 2145978922581353981609495)
              ·
                refine ⟨3218968383872030972414243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145978922581353981609495 3218968383872030972414243)
                ·
                  refine ⟨4828452575808046458621365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218968383872030972414243 4828452575808046458621365)
                  ·
                    refine ⟨452667428982004355495753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4828452575808046458621365 452667428982004355495753)
                    ·
                      rfl

theorem cell22_1322350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1322350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322350 prefixEnd_1322350 := by exact prefixLift 1322350
  have htrace : WordTrace (prefixWord ++ tailWord_1322350) baseStart_1322350 baseEnd_1322350 := by
    simpa [prefixWord, tailWord_1322350, baseEnd_1322350] using wordTrace_append hprefix tailTrace_1322350
  have hstable : (prefixWord ++ tailWord_1322350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322350).length < 2 ^ (prefixWord ++ tailWord_1322350).sum := by decide
  have hdescent : baseEnd_1322350 < baseStart_1322350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322404 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_1322404 : Nat := 118140960795 + 1322404 * 2 ^ 59
def prefixEnd_1322404 : Nat := 4983230072969 + 3 ^ 40 * 1322404 * 2
def baseEnd_1322404 : Nat := 452685914285566214645587

theorem tailTrace_1322404 : CollatzResearch.WordTrace tailWord_1322404 prefixEnd_1322404 452685914285566214645587 := by
  unfold tailWord_1322404
  simp only [CollatzResearch.WordTrace]
  refine ⟨24116018150581815733791133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32154690867442420978388177 24116018150581815733791133)
  ·
    refine ⟨9043506806468180900171675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24116018150581815733791133 9043506806468180900171675)
    ·
      refine ⟨13565260209702271350257513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9043506806468180900171675 13565260209702271350257513)
      ·
        refine ⟨10173945157276703512693135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13565260209702271350257513 10173945157276703512693135)
        ·
          refine ⟨15260917735915055269039703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10173945157276703512693135 15260917735915055269039703)
          ·
            refine ⟨22891376603872582903559555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15260917735915055269039703 22891376603872582903559555)
            ·
              refine ⟨34337064905808874355339333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22891376603872582903559555 34337064905808874355339333)
              ·
                refine ⟨6438199669839163941626125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34337064905808874355339333 6438199669839163941626125)
                ·
                  refine ⟨2414324876189686478109797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6438199669839163941626125 2414324876189686478109797)
                  ·
                    refine ⟨452685914285566214645587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2414324876189686478109797 452685914285566214645587)
                    ·
                      rfl

theorem cell22_1322404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_1322404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322404 prefixEnd_1322404 := by exact prefixLift 1322404
  have htrace : WordTrace (prefixWord ++ tailWord_1322404) baseStart_1322404 baseEnd_1322404 := by
    simpa [prefixWord, tailWord_1322404, baseEnd_1322404] using wordTrace_append hprefix tailTrace_1322404
  have hstable : (prefixWord ++ tailWord_1322404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322404).length < 2 ^ (prefixWord ++ tailWord_1322404).sum := by decide
  have hdescent : baseEnd_1322404 < baseStart_1322404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322408 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 5]
def baseStart_1322408 : Nat := 118140960795 + 1322408 * 2 ^ 59
def prefixEnd_1322408 : Nat := 4983230072969 + 3 ^ 40 * 1322408 * 2
def baseEnd_1322408 : Nat := 150895761189103845848525

theorem tailTrace_1322408 : CollatzResearch.WordTrace tailWord_1322408 prefixEnd_1322408 150895761189103845848525 := by
  unfold tailWord_1322408
  simp only [CollatzResearch.WordTrace]
  refine ⟨24116091096574570075363939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32154788128766093433818585 24116091096574570075363939)
  ·
    refine ⟨36174136644861855113045909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24116091096574570075363939 36174136644861855113045909)
    ·
      refine ⟨1695662655227899458424027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36174136644861855113045909 1695662655227899458424027)
      ·
        refine ⟨2543493982841849187636041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695662655227899458424027 2543493982841849187636041)
        ·
          refine ⟨1907620487131386890727031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2543493982841849187636041 1907620487131386890727031)
          ·
            refine ⟨2861430730697080336090547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907620487131386890727031 2861430730697080336090547)
            ·
              refine ⟨4292146096045620504135821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861430730697080336090547 4292146096045620504135821)
              ·
                refine ⟨1609554786017107689050933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4292146096045620504135821 1609554786017107689050933)
                ·
                  refine ⟨150895761189103845848525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1609554786017107689050933 150895761189103845848525)
                  ·
                    rfl

theorem cell22_1322408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_1322408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322408 prefixEnd_1322408 := by exact prefixLift 1322408
  have htrace : WordTrace (prefixWord ++ tailWord_1322408) baseStart_1322408 baseEnd_1322408 := by
    simpa [prefixWord, tailWord_1322408, baseEnd_1322408] using wordTrace_append hprefix tailTrace_1322408
  have hstable : (prefixWord ++ tailWord_1322408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322408).length < 2 ^ (prefixWord ++ tailWord_1322408).sum := by decide
  have hdescent : baseEnd_1322408 < baseStart_1322408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322421 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1322421 : Nat := 118140960795 + 1322421 * 2 ^ 59
def prefixEnd_1322421 : Nat := 4983230072969 + 3 ^ 40 * 1322421 * 2
def baseEnd_1322421 : Nat := 452691733732983836970535

theorem tailTrace_1322421 : CollatzResearch.WordTrace tailWord_1322421 prefixEnd_1322421 452691733732983836970535 := by
  unfold tailWord_1322421
  simp only [CollatzResearch.WordTrace]
  refine ⟨48232656342102043370951117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32155104228068028913967411 48232656342102043370951117)
  ·
    refine ⟨18087246128288266264106669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48232656342102043370951117 18087246128288266264106669)
    ·
      refine ⟨6782717298108099849040001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18087246128288266264106669 6782717298108099849040001)
      ·
        refine ⟨5087037973581074886780001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6782717298108099849040001 5087037973581074886780001)
        ·
          refine ⟨3815278480185806165085001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5087037973581074886780001 3815278480185806165085001)
          ·
            refine ⟨2861458860139354623813751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3815278480185806165085001 2861458860139354623813751)
            ·
              refine ⟨4292188290209031935720627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861458860139354623813751 4292188290209031935720627)
              ·
                refine ⟨6438282435313547903580941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292188290209031935720627 6438282435313547903580941)
                ·
                  refine ⟨2414355913242580463842853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6438282435313547903580941 2414355913242580463842853)
                  ·
                    refine ⟨452691733732983836970535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2414355913242580463842853 452691733732983836970535)
                    ·
                      rfl

theorem cell22_1322421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1322421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322421 prefixEnd_1322421 := by exact prefixLift 1322421
  have htrace : WordTrace (prefixWord ++ tailWord_1322421) baseStart_1322421 baseEnd_1322421 := by
    simpa [prefixWord, tailWord_1322421, baseEnd_1322421] using wordTrace_append hprefix tailTrace_1322421
  have hstable : (prefixWord ++ tailWord_1322421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322421).length < 2 ^ (prefixWord ++ tailWord_1322421).sum := by decide
  have hdescent : baseEnd_1322421 < baseStart_1322421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322481 : List Nat := [1, 2, 2, 2, 3, 3, 3, 6]
def baseStart_1322481 : Nat := 118140960795 + 1322481 * 2 ^ 59
def prefixEnd_1322481 : Nat := 4983230072969 + 3 ^ 40 * 1322481 * 2
def baseEnd_1322481 : Nat := 50301363662129297830039

theorem tailTrace_1322481 : CollatzResearch.WordTrace tailWord_1322481 prefixEnd_1322481 50301363662129297830039 := by
  unfold tailWord_1322481
  simp only [CollatzResearch.WordTrace]
  refine ⟨48234844721884673618135297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32156563147923115745423531 48234844721884673618135297)
  ·
    refine ⟨36176133541413505213601473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48234844721884673618135297 36176133541413505213601473)
    ·
      refine ⟨27132100156060128910201105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36176133541413505213601473 27132100156060128910201105)
      ·
        refine ⟨20349075117045096682650829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27132100156060128910201105 20349075117045096682650829)
        ·
          refine ⟨7630903168891911255994061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20349075117045096682650829 7630903168891911255994061)
          ·
            refine ⟨2861588688334466720997773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7630903168891911255994061 2861588688334466720997773)
            ·
              refine ⟨1073095758125425020374165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2861588688334466720997773 1073095758125425020374165)
              ·
                refine ⟨50301363662129297830039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1073095758125425020374165 50301363662129297830039)
                ·
                  rfl

theorem cell22_1322481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 6].length) (baseStart_1322481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322481 prefixEnd_1322481 := by exact prefixLift 1322481
  have htrace : WordTrace (prefixWord ++ tailWord_1322481) baseStart_1322481 baseEnd_1322481 := by
    simpa [prefixWord, tailWord_1322481, baseEnd_1322481] using wordTrace_append hprefix tailTrace_1322481
  have hstable : (prefixWord ++ tailWord_1322481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322481).length < 2 ^ (prefixWord ++ tailWord_1322481).sum := by decide
  have hdescent : baseEnd_1322481 < baseStart_1322481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322513 : List Nat := [1, 2, 2, 1, 1, 2, 3, 6, 1, 3]
def baseStart_1322513 : Nat := 118140960795 + 1322513 * 2 ^ 59
def prefixEnd_1322513 : Nat := 4983230072969 + 3 ^ 40 * 1322513 * 2
def baseEnd_1322513 : Nat := 452723227213126263670253

theorem tailTrace_1322513 : CollatzResearch.WordTrace tailWord_1322513 prefixEnd_1322513 452723227213126263670253 := by
  unfold tailWord_1322513
  simp only [CollatzResearch.WordTrace]
  refine ⟨48236011857768743083300193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32157341238512495388866795 48236011857768743083300193)
  ·
    refine ⟨36177008893326557312475145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48236011857768743083300193 36177008893326557312475145)
    ·
      refine ⟨27132756669994917984356359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36177008893326557312475145 27132756669994917984356359)
      ·
        refine ⟨40699135004992376976534539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27132756669994917984356359 40699135004992376976534539)
        ·
          refine ⟨61048702507488565464801809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40699135004992376976534539 61048702507488565464801809)
          ·
            refine ⟨45786526880616424098601357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61048702507488565464801809 45786526880616424098601357)
            ·
              refine ⟨17169947580231159036975509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45786526880616424098601357 17169947580231159036975509)
              ·
                refine ⟨804841292823335579858227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17169947580231159036975509 804841292823335579858227)
                ·
                  refine ⟨1207261939235003369787341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804841292823335579858227 1207261939235003369787341)
                  ·
                    refine ⟨452723227213126263670253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1207261939235003369787341 452723227213126263670253)
                    ·
                      rfl

theorem cell22_1322513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_1322513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322513 prefixEnd_1322513 := by exact prefixLift 1322513
  have htrace : WordTrace (prefixWord ++ tailWord_1322513) baseStart_1322513 baseEnd_1322513 := by
    simpa [prefixWord, tailWord_1322513, baseEnd_1322513] using wordTrace_append hprefix tailTrace_1322513
  have hstable : (prefixWord ++ tailWord_1322513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322513).length < 2 ^ (prefixWord ++ tailWord_1322513).sum := by decide
  have hdescent : baseEnd_1322513 < baseStart_1322513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322601 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_1322601 : Nat := 118140960795 + 1322601 * 2 ^ 59
def prefixEnd_1322601 : Nat := 4983230072969 + 3 ^ 40 * 1322601 * 2
def baseEnd_1322601 : Nat := 452753351411523367469983

theorem tailTrace_1322601 : CollatzResearch.WordTrace tailWord_1322601 prefixEnd_1322601 452753351411523367469983 := by
  unfold tailWord_1322601
  simp only [CollatzResearch.WordTrace]
  refine ⟨48239221481449934112503657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32159480987633289408335771 48239221481449934112503657)
  ·
    refine ⟨36179416111087450584377743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48239221481449934112503657 36179416111087450584377743)
    ·
      refine ⟨54269124166631175876566615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36179416111087450584377743 54269124166631175876566615)
      ·
        refine ⟨81403686249946763814849923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54269124166631175876566615 81403686249946763814849923)
        ·
          refine ⟨122105529374920145722274885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81403686249946763814849923 122105529374920145722274885)
          ·
            refine ⟨22894786757797527322926541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122105529374920145722274885 22894786757797527322926541)
            ·
              refine ⟨8585545034174072746097453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22894786757797527322926541 8585545034174072746097453)
              ·
                refine ⟨3219579387815277279786545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8585545034174072746097453 3219579387815277279786545)
                ·
                  refine ⟨2414684540861457959839909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3219579387815277279786545 2414684540861457959839909)
                  ·
                    refine ⟨452753351411523367469983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2414684540861457959839909 452753351411523367469983)
                    ·
                      rfl

theorem cell22_1322601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_1322601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322601 prefixEnd_1322601 := by exact prefixLift 1322601
  have htrace : WordTrace (prefixWord ++ tailWord_1322601) baseStart_1322601 baseEnd_1322601 := by
    simpa [prefixWord, tailWord_1322601, baseEnd_1322601] using wordTrace_append hprefix tailTrace_1322601
  have hstable : (prefixWord ++ tailWord_1322601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322601).length < 2 ^ (prefixWord ++ tailWord_1322601).sum := by decide
  have hdescent : baseEnd_1322601 < baseStart_1322601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322648 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1322648 : Nat := 118140960795 + 1322648 * 2 ^ 59
def prefixEnd_1322648 : Nat := 4983230072969 + 3 ^ 40 * 1322648 * 2
def baseEnd_1322648 : Nat := 452769440472030911544839

theorem tailTrace_1322648 : CollatzResearch.WordTrace tailWord_1322648 prefixEnd_1322648 452769440472030911544839 := by
  unfold tailWord_1322648
  simp only [CollatzResearch.WordTrace]
  refine ⟨24120467856139830569732299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32160623808186440759643065 24120467856139830569732299)
  ·
    refine ⟨36180701784209745854598449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24120467856139830569732299 36180701784209745854598449)
    ·
      refine ⟨27135526338157309390948837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36180701784209745854598449 27135526338157309390948837)
      ·
        refine ⟨5087911188404495510802907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27135526338157309390948837 5087911188404495510802907)
        ·
          refine ⟨7631866782606743266204361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5087911188404495510802907 7631866782606743266204361)
          ·
            refine ⟨5723900086955057449653271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7631866782606743266204361 5723900086955057449653271)
            ·
              refine ⟨8585850130432586174479907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5723900086955057449653271 8585850130432586174479907)
              ·
                refine ⟨12878775195648879261719861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8585850130432586174479907 12878775195648879261719861)
                ·
                  refine ⟨1207385174592082430786237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12878775195648879261719861 1207385174592082430786237)
                  ·
                    refine ⟨452769440472030911544839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1207385174592082430786237 452769440472030911544839)
                    ·
                      rfl

theorem cell22_1322648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1322648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322648 prefixEnd_1322648 := by exact prefixLift 1322648
  have htrace : WordTrace (prefixWord ++ tailWord_1322648) baseStart_1322648 baseEnd_1322648 := by
    simpa [prefixWord, tailWord_1322648, baseEnd_1322648] using wordTrace_append hprefix tailTrace_1322648
  have hstable : (prefixWord ++ tailWord_1322648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322648).length < 2 ^ (prefixWord ++ tailWord_1322648).sum := by decide
  have hdescent : baseEnd_1322648 < baseStart_1322648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322652 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1322652 : Nat := 118140960795 + 1322652 * 2 ^ 59
def prefixEnd_1322652 : Nat := 4983230072969 + 3 ^ 40 * 1322652 * 2
def baseEnd_1322652 : Nat := 452770809753776234444827

theorem tailTrace_1322652 : CollatzResearch.WordTrace tailWord_1322652 prefixEnd_1322652 452770809753776234444827 := by
  unfold tailWord_1322652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24120540802132584911305105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32160721069510113215073473 24120540802132584911305105)
  ·
    refine ⟨18090405601599438683478829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24120540802132584911305105 18090405601599438683478829)
    ·
      refine ⟨6783902100599789506304561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18090405601599438683478829 6783902100599789506304561)
      ·
        refine ⟨5087926575449842129728421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6783902100599789506304561 5087926575449842129728421)
        ·
          refine ⟨953986232896845399324079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5087926575449842129728421 953986232896845399324079)
          ·
            refine ⟨1430979349345268098986119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953986232896845399324079 1430979349345268098986119)
            ·
              refine ⟨2146469024017902148479179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430979349345268098986119 2146469024017902148479179)
              ·
                refine ⟨3219703536026853222718769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146469024017902148479179 3219703536026853222718769)
                ·
                  refine ⟨2414777652020139917039077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3219703536026853222718769 2414777652020139917039077)
                  ·
                    refine ⟨452770809753776234444827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2414777652020139917039077 452770809753776234444827)
                    ·
                      rfl

theorem cell22_1322652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1322652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322652 prefixEnd_1322652 := by exact prefixLift 1322652
  have htrace : WordTrace (prefixWord ++ tailWord_1322652) baseStart_1322652 baseEnd_1322652 := by
    simpa [prefixWord, tailWord_1322652, baseEnd_1322652] using wordTrace_append hprefix tailTrace_1322652
  have hstable : (prefixWord ++ tailWord_1322652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322652).length < 2 ^ (prefixWord ++ tailWord_1322652).sum := by decide
  have hdescent : baseEnd_1322652 < baseStart_1322652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322716 : List Nat := [2, 2, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1322716 : Nat := 118140960795 + 1322716 * 2 ^ 59
def prefixEnd_1322716 : Nat := 4983230072969 + 3 ^ 40 * 1322716 * 2
def baseEnd_1322716 : Nat := 452792718261701400844631

theorem tailTrace_1322716 : CollatzResearch.WordTrace tailWord_1322716 prefixEnd_1322716 452792718261701400844631 := by
  unfold tailWord_1322716
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121707938016654376470001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32162277250688872501960001 24121707938016654376470001)
  ·
    refine ⟨18091280953512490782352501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24121707938016654376470001 18091280953512490782352501)
    ·
      refine ⟨1696057589391796010845547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18091280953512490782352501 1696057589391796010845547)
      ·
        refine ⟨2544086384087694016268321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696057589391796010845547 2544086384087694016268321)
        ·
          refine ⟨1908064788065770512201241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2544086384087694016268321 1908064788065770512201241)
          ·
            refine ⟨1431048591049327884150931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1908064788065770512201241 1431048591049327884150931)
            ·
              refine ⟨2146572886573991826226397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431048591049327884150931 2146572886573991826226397)
              ·
                refine ⟨804964832465246934834899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2146572886573991826226397 804964832465246934834899)
                ·
                  refine ⟨1207447248697870402252349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804964832465246934834899 1207447248697870402252349)
                  ·
                    refine ⟨452792718261701400844631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1207447248697870402252349 452792718261701400844631)
                    ·
                      rfl

theorem cell22_1322716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1322716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322716 prefixEnd_1322716 := by exact prefixLift 1322716
  have htrace : WordTrace (prefixWord ++ tailWord_1322716) baseStart_1322716 baseEnd_1322716 := by
    simpa [prefixWord, tailWord_1322716, baseEnd_1322716] using wordTrace_append hprefix tailTrace_1322716
  have hstable : (prefixWord ++ tailWord_1322716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322716).length < 2 ^ (prefixWord ++ tailWord_1322716).sum := by decide
  have hdescent : baseEnd_1322716 < baseStart_1322716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322736 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_1322736 : Nat := 118140960795 + 1322736 * 2 ^ 59
def prefixEnd_1322736 : Nat := 4983230072969 + 3 ^ 40 * 1322736 * 2
def baseEnd_1322736 : Nat := 452799564670428015344569

theorem tailTrace_1322736 : CollatzResearch.WordTrace tailWord_1322736 prefixEnd_1322736 452799564670428015344569 := by
  unfold tailWord_1322736
  simp only [CollatzResearch.WordTrace]
  refine ⟨24122072667980426084334031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32162763557307234779112041 24122072667980426084334031)
  ·
    refine ⟨36183109001970639126501047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24122072667980426084334031 36183109001970639126501047)
    ·
      refine ⟨54274663502955958689751571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36183109001970639126501047 54274663502955958689751571)
      ·
        refine ⟨81411995254433938034627357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54274663502955958689751571 81411995254433938034627357)
        ·
          refine ⟨30529498220412726762985259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81411995254433938034627357 30529498220412726762985259)
          ·
            refine ⟨45794247330619090144477889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30529498220412726762985259 45794247330619090144477889)
            ·
              refine ⟨34345685497964317608358417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45794247330619090144477889 34345685497964317608358417)
              ·
                refine ⟨25759264123473238206268813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34345685497964317608358417 25759264123473238206268813)
                ·
                  refine ⟨9659724046302464327350805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25759264123473238206268813 9659724046302464327350805)
                  ·
                    refine ⟨452799564670428015344569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9659724046302464327350805 452799564670428015344569)
                    ·
                      rfl

theorem cell22_1322736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_1322736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322736 prefixEnd_1322736 := by exact prefixLift 1322736
  have htrace : WordTrace (prefixWord ++ tailWord_1322736) baseStart_1322736 baseEnd_1322736 := by
    simpa [prefixWord, tailWord_1322736, baseEnd_1322736] using wordTrace_append hprefix tailTrace_1322736
  have hstable : (prefixWord ++ tailWord_1322736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322736).length < 2 ^ (prefixWord ++ tailWord_1322736).sum := by decide
  have hdescent : baseEnd_1322736 < baseStart_1322736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322751 : List Nat := [1, 1, 2, 2, 1, 3, 3, 9]
def baseStart_1322751 : Nat := 118140960795 + 1322751 * 2 ^ 59
def prefixEnd_1322751 : Nat := 4983230072969 + 3 ^ 40 * 1322751 * 2
def baseEnd_1322751 : Nat := 50311633275219219579947

theorem tailTrace_1322751 : CollatzResearch.WordTrace tailWord_1322751 prefixEnd_1322751 50311633275219219579947 := by
  unfold tailWord_1322751
  simp only [CollatzResearch.WordTrace]
  refine ⟨48244692430906509730464107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32163128287271006486976071 48244692430906509730464107)
  ·
    refine ⟨72367038646359764595696161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48244692430906509730464107 72367038646359764595696161)
    ·
      refine ⟨54275278984769823446772121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72367038646359764595696161 54275278984769823446772121)
      ·
        refine ⟨40706459238577367585079091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54275278984769823446772121 40706459238577367585079091)
        ·
          refine ⟨61059688857866051377618637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40706459238577367585079091 61059688857866051377618637)
          ·
            refine ⟨22897383321699769266606989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61059688857866051377618637 22897383321699769266606989)
            ·
              refine ⟨8586518745637413474977621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22897383321699769266606989 8586518745637413474977621)
              ·
                refine ⟨50311633275219219579947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8586518745637413474977621 50311633275219219579947)
                ·
                  rfl

theorem cell22_1322751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 9].length) (baseStart_1322751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322751 prefixEnd_1322751 := by exact prefixLift 1322751
  have htrace : WordTrace (prefixWord ++ tailWord_1322751) baseStart_1322751 baseEnd_1322751 := by
    simpa [prefixWord, tailWord_1322751, baseEnd_1322751] using wordTrace_append hprefix tailTrace_1322751
  have hstable : (prefixWord ++ tailWord_1322751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322751).length < 2 ^ (prefixWord ++ tailWord_1322751).sum := by decide
  have hdescent : baseEnd_1322751 < baseStart_1322751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322759 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 1, 4]
def baseStart_1322759 : Nat := 118140960795 + 1322759 * 2 ^ 59
def prefixEnd_1322759 : Nat := 4983230072969 + 3 ^ 40 * 1322759 * 2
def baseEnd_1322759 : Nat := 452807438040463622019499

theorem tailTrace_1322759 : CollatzResearch.WordTrace tailWord_1322759 prefixEnd_1322759 452807438040463622019499 := by
  unfold tailWord_1322759
  simp only [CollatzResearch.WordTrace]
  refine ⟨48244984214877527096755331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32163322809918351397836887 48244984214877527096755331)
  ·
    refine ⟨72367476322316290645132997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48244984214877527096755331 72367476322316290645132997)
    ·
      refine ⟨13568901810434304495962437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72367476322316290645132997 13568901810434304495962437)
      ·
        refine ⟨2544169089456432092992957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13568901810434304495962437 2544169089456432092992957)
        ·
          refine ⟨954063408546162034872359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2544169089456432092992957 954063408546162034872359)
          ·
            refine ⟨1431095112819243052308539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954063408546162034872359 1431095112819243052308539)
            ·
              refine ⟨2146642669228864578462809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431095112819243052308539 2146642669228864578462809)
              ·
                refine ⟨1609982001921648433847107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146642669228864578462809 1609982001921648433847107)
                ·
                  refine ⟨2414973002882472650770661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609982001921648433847107 2414973002882472650770661)
                  ·
                    refine ⟨452807438040463622019499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2414973002882472650770661 452807438040463622019499)
                    ·
                      rfl

theorem cell22_1322759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_1322759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322759 prefixEnd_1322759 := by exact prefixLift 1322759
  have htrace : WordTrace (prefixWord ++ tailWord_1322759) baseStart_1322759 baseEnd_1322759 := by
    simpa [prefixWord, tailWord_1322759, baseEnd_1322759] using wordTrace_append hprefix tailTrace_1322759
  have hstable : (prefixWord ++ tailWord_1322759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322759).length < 2 ^ (prefixWord ++ tailWord_1322759).sum := by decide
  have hdescent : baseEnd_1322759 < baseStart_1322759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322834 : List Nat := [3, 2, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_1322834 : Nat := 118140960795 + 1322834 * 2 ^ 59
def prefixEnd_1322834 : Nat := 4983230072969 + 3 ^ 40 * 1322834 * 2
def baseEnd_1322834 : Nat := 452833112073188426394269

theorem tailTrace_1322834 : CollatzResearch.WordTrace tailWord_1322834 prefixEnd_1322834 452833112073188426394269 := by
  unfold tailWord_1322834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12061929922401453726433889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32165146459737209937157037 12061929922401453726433889)
  ·
    refine ⟨9046447441801090294825417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12061929922401453726433889 9046447441801090294825417)
    ·
      refine ⟨6784835581350817721119063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9046447441801090294825417 6784835581350817721119063)
      ·
        refine ⟨10177253372026226581678595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784835581350817721119063 10177253372026226581678595)
        ·
          refine ⟨15265880058039339872517893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10177253372026226581678595 15265880058039339872517893)
          ·
            refine ⟨2862352510882376226097105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15265880058039339872517893 2862352510882376226097105)
            ·
              refine ⟨2146764383161782169572829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2862352510882376226097105 2146764383161782169572829)
              ·
                refine ⟨805036643685668313589811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2146764383161782169572829 805036643685668313589811)
                ·
                  refine ⟨1207554965528502470384717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805036643685668313589811 1207554965528502470384717)
                  ·
                    refine ⟨452833112073188426394269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1207554965528502470384717 452833112073188426394269)
                    ·
                      rfl

theorem cell22_1322834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_1322834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322834 prefixEnd_1322834 := by exact prefixLift 1322834
  have htrace : WordTrace (prefixWord ++ tailWord_1322834) baseStart_1322834 baseEnd_1322834 := by
    simpa [prefixWord, tailWord_1322834, baseEnd_1322834] using wordTrace_append hprefix tailTrace_1322834
  have hstable : (prefixWord ++ tailWord_1322834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322834).length < 2 ^ (prefixWord ++ tailWord_1322834).sum := by decide
  have hdescent : baseEnd_1322834 < baseStart_1322834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322903 : List Nat := [1, 1, 3, 3, 1, 3, 10]
def baseStart_1322903 : Nat := 118140960795 + 1322903 * 2 ^ 59
def prefixEnd_1322903 : Nat := 4983230072969 + 3 ^ 40 * 1322903 * 2
def baseEnd_1322903 : Nat := 16772471562344268385891

theorem tailTrace_1322903 : CollatzResearch.WordTrace tailWord_1322903 prefixEnd_1322903 16772471562344268385891 := by
  unfold tailWord_1322903
  simp only [CollatzResearch.WordTrace]
  refine ⟨48250236326355839689997363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32166824217570559793331575 48250236326355839689997363)
  ·
    refine ⟨72375354489533759534996045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48250236326355839689997363 72375354489533759534996045)
    ·
      refine ⟨27140757933575159825623517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72375354489533759534996045 27140757933575159825623517)
      ·
        refine ⟨10177784225090684934608819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27140757933575159825623517 10177784225090684934608819)
        ·
          refine ⟨15266676337636027401913229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10177784225090684934608819 15266676337636027401913229)
          ·
            refine ⟨5725003626613510275717461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15266676337636027401913229 5725003626613510275717461)
            ·
              refine ⟨16772471562344268385891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5725003626613510275717461 16772471562344268385891)
              ·
                rfl

theorem cell22_1322903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 10].length) (baseStart_1322903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322903 prefixEnd_1322903 := by exact prefixLift 1322903
  have htrace : WordTrace (prefixWord ++ tailWord_1322903) baseStart_1322903 baseEnd_1322903 := by
    simpa [prefixWord, tailWord_1322903, baseEnd_1322903] using wordTrace_append hprefix tailTrace_1322903
  have hstable : (prefixWord ++ tailWord_1322903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322903).length < 2 ^ (prefixWord ++ tailWord_1322903).sum := by decide
  have hdescent : baseEnd_1322903 < baseStart_1322903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322909 : List Nat := [1, 4, 2, 1, 2, 3, 3, 2, 4]
def baseStart_1322909 : Nat := 118140960795 + 1322909 * 2 ^ 59
def prefixEnd_1322909 : Nat := 4983230072969 + 3 ^ 40 * 1322909 * 2
def baseEnd_1322909 : Nat := 150952928701971076923013

theorem tailTrace_1322909 : CollatzResearch.WordTrace tailWord_1322909 prefixEnd_1322909 150952928701971076923013 := by
  unfold tailWord_1322909
  simp only [CollatzResearch.WordTrace]
  refine ⟨48250455164334102714715781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32166970109556068476477187 48250455164334102714715781)
  ·
    refine ⟨9046960343312644259009209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48250455164334102714715781 9046960343312644259009209)
    ·
      refine ⟨6785220257484483194256907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9046960343312644259009209 6785220257484483194256907)
      ·
        refine ⟨10177830386226724791385361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6785220257484483194256907 10177830386226724791385361)
        ·
          refine ⟨7633372789670043593539021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10177830386226724791385361 7633372789670043593539021)
          ·
            refine ⟨2862514796126266347577133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7633372789670043593539021 2862514796126266347577133)
            ·
              refine ⟨1073443048547349880341425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2862514796126266347577133 1073443048547349880341425)
              ·
                refine ⟨805082286410512410256069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1073443048547349880341425 805082286410512410256069)
                ·
                  refine ⟨150952928701971076923013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805082286410512410256069 150952928701971076923013)
                  ·
                    rfl

theorem cell22_1322909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_1322909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322909 prefixEnd_1322909 := by exact prefixLift 1322909
  have htrace : WordTrace (prefixWord ++ tailWord_1322909) baseStart_1322909 baseEnd_1322909 := by
    simpa [prefixWord, tailWord_1322909, baseEnd_1322909] using wordTrace_append hprefix tailTrace_1322909
  have hstable : (prefixWord ++ tailWord_1322909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322909).length < 2 ^ (prefixWord ++ tailWord_1322909).sum := by decide
  have hdescent : baseEnd_1322909 < baseStart_1322909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322935 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 5, 3]
def baseStart_1322935 : Nat := 118140960795 + 1322935 * 2 ^ 59
def prefixEnd_1322935 : Nat := 4983230072969 + 3 ^ 40 * 1322935 * 2
def baseEnd_1322935 : Nat := 452867686437257829618959

theorem tailTrace_1322935 : CollatzResearch.WordTrace tailWord_1322935 prefixEnd_1322935 452867686437257829618959 := by
  unfold tailWord_1322935
  simp only [CollatzResearch.WordTrace]
  refine ⟨48251403462239909155162259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32167602308159939436774839 48251403462239909155162259)
  ·
    refine ⟨72377105193359863732743389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48251403462239909155162259 72377105193359863732743389)
    ·
      refine ⟨27141414447509948899778771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72377105193359863732743389 27141414447509948899778771)
      ·
        refine ⟨40712121671264923349668157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27141414447509948899778771 40712121671264923349668157)
        ·
          refine ⟨15267045626724346256125559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40712121671264923349668157 15267045626724346256125559)
          ·
            refine ⟨22900568440086519384188339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15267045626724346256125559 22900568440086519384188339)
            ·
              refine ⟨34350852660129779076282509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22900568440086519384188339 34350852660129779076282509)
              ·
                refine ⟨12881569747548667153605941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34350852660129779076282509 12881569747548667153605941)
                ·
                  refine ⟨1207647163832687545650557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12881569747548667153605941 1207647163832687545650557)
                  ·
                    refine ⟨452867686437257829618959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1207647163832687545650557 452867686437257829618959)
                    ·
                      rfl

theorem cell22_1322935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_1322935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322935 prefixEnd_1322935 := by exact prefixLift 1322935
  have htrace : WordTrace (prefixWord ++ tailWord_1322935) baseStart_1322935 baseEnd_1322935 := by
    simpa [prefixWord, tailWord_1322935, baseEnd_1322935] using wordTrace_append hprefix tailTrace_1322935
  have hstable : (prefixWord ++ tailWord_1322935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322935).length < 2 ^ (prefixWord ++ tailWord_1322935).sum := by decide
  have hdescent : baseEnd_1322935 < baseStart_1322935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1322980 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_1322980 : Nat := 118140960795 + 1322980 * 2 ^ 59
def prefixEnd_1322980 : Nat := 4983230072969 + 3 ^ 40 * 1322980 * 2
def baseEnd_1322980 : Nat := 452883090856892712243821

theorem tailTrace_1322980 : CollatzResearch.WordTrace tailWord_1322980 prefixEnd_1322980 452883090856892712243821 := by
  unfold tailWord_1322980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24126522373538440920275197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32168696498051254560366929 24126522373538440920275197)
  ·
    refine ⟨9047445890076915345103199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24126522373538440920275197 9047445890076915345103199)
    ·
      refine ⟨13571168835115373017654799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9047445890076915345103199 13571168835115373017654799)
      ·
        refine ⟨20356753252673059526482199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13571168835115373017654799 20356753252673059526482199)
        ·
          refine ⟨30535129879009589289723299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20356753252673059526482199 30535129879009589289723299)
          ·
            refine ⟨45802694818514383934584949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30535129879009589289723299 45802694818514383934584949)
            ·
              refine ⟨4294002639235723493867339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45802694818514383934584949 4294002639235723493867339)
              ·
                refine ⟨6441003958853585240801009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294002639235723493867339 6441003958853585240801009)
                ·
                  refine ⟨4830752969140188930600757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6441003958853585240801009 4830752969140188930600757)
                  ·
                    refine ⟨452883090856892712243821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4830752969140188930600757 452883090856892712243821)
                    ·
                      rfl

theorem cell22_1322980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_1322980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1322980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1322980 prefixEnd_1322980 := by exact prefixLift 1322980
  have htrace : WordTrace (prefixWord ++ tailWord_1322980) baseStart_1322980 baseEnd_1322980 := by
    simpa [prefixWord, tailWord_1322980, baseEnd_1322980] using wordTrace_append hprefix tailTrace_1322980
  have hstable : (prefixWord ++ tailWord_1322980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1322980).length < 2 ^ (prefixWord ++ tailWord_1322980).sum := by decide
  have hdescent : baseEnd_1322980 < baseStart_1322980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1322980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323027 : List Nat := [1, 1, 1, 2, 1, 4, 4, 4, 4]
def baseStart_1323027 : Nat := 118140960795 + 1323027 * 2 ^ 59
def prefixEnd_1323027 : Nat := 4983230072969 + 3 ^ 40 * 1323027 * 2
def baseEnd_1323027 : Nat := 150966393305800085439559

theorem tailTrace_1323027 : CollatzResearch.WordTrace tailWord_1323027 prefixEnd_1323027 150966393305800085439559 := by
  unfold tailWord_1323027
  simp only [CollatzResearch.WordTrace]
  refine ⟨48254758977906608867511335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32169839318604405911674223 48254758977906608867511335)
  ·
    refine ⟨72382138466859913301267003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48254758977906608867511335 72382138466859913301267003)
    ·
      refine ⟨108573207700289869951900505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72382138466859913301267003 108573207700289869951900505)
      ·
        refine ⟨81429905775217402463925379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108573207700289869951900505 81429905775217402463925379)
        ·
          refine ⟨122144858662826103695888069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81429905775217402463925379 122144858662826103695888069)
          ·
            refine ⟨22902160999279894442979013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122144858662826103695888069 22902160999279894442979013)
            ·
              refine ⟨4294155187364980208058565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22902160999279894442979013 4294155187364980208058565)
              ·
                refine ⟨805154097630933789010981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4294155187364980208058565 805154097630933789010981)
                ·
                  refine ⟨150966393305800085439559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805154097630933789010981 150966393305800085439559)
                  ·
                    rfl

theorem cell22_1323027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 4].length) (baseStart_1323027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323027 prefixEnd_1323027 := by exact prefixLift 1323027
  have htrace : WordTrace (prefixWord ++ tailWord_1323027) baseStart_1323027 baseEnd_1323027 := by
    simpa [prefixWord, tailWord_1323027, baseEnd_1323027] using wordTrace_append hprefix tailTrace_1323027
  have hstable : (prefixWord ++ tailWord_1323027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323027).length < 2 ^ (prefixWord ++ tailWord_1323027).sum := by decide
  have hdescent : baseEnd_1323027 < baseStart_1323027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323078 : List Nat := [6, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1323078 : Nat := 118140960795 + 1323078 * 2 ^ 59
def prefixEnd_1323078 : Nat := 4983230072969 + 3 ^ 40 * 1323078 * 2
def baseEnd_1323078 : Nat := 150972212753217707764507

theorem tailTrace_1323078 : CollatzResearch.WordTrace tailWord_1323078 prefixEnd_1323078 150972212753217707764507 := by
  unfold tailWord_1323078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508019346897557643050559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32171079400481229718411925 1508019346897557643050559)
  ·
    refine ⟨2262029020346336464575839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508019346897557643050559 2262029020346336464575839)
    ·
      refine ⟨3393043530519504696863759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262029020346336464575839 3393043530519504696863759)
      ·
        refine ⟨5089565295779257045295639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393043530519504696863759 5089565295779257045295639)
        ·
          refine ⟨7634347943668885567943459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5089565295779257045295639 7634347943668885567943459)
          ·
            refine ⟨11451521915503328351915189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634347943668885567943459 11451521915503328351915189)
            ·
              refine ⟨1073580179578437032992049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11451521915503328351915189 1073580179578437032992049)
              ·
                refine ⟨805185134683827774744037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1073580179578437032992049 805185134683827774744037)
                ·
                  refine ⟨150972212753217707764507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805185134683827774744037 150972212753217707764507)
                  ·
                    rfl

theorem cell22_1323078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1323078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323078 prefixEnd_1323078 := by exact prefixLift 1323078
  have htrace : WordTrace (prefixWord ++ tailWord_1323078) baseStart_1323078 baseEnd_1323078 := by
    simpa [prefixWord, tailWord_1323078, baseEnd_1323078] using wordTrace_append hprefix tailTrace_1323078
  have hstable : (prefixWord ++ tailWord_1323078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323078).length < 2 ^ (prefixWord ++ tailWord_1323078).sum := by decide
  have hdescent : baseEnd_1323078 < baseStart_1323078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323164 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1323164 : Nat := 118140960795 + 1323164 * 2 ^ 59
def prefixEnd_1323164 : Nat := 4983230072969 + 3 ^ 40 * 1323164 * 2
def baseEnd_1323164 : Nat := 452946077817177565643257

theorem tailTrace_1323164 : CollatzResearch.WordTrace tailWord_1323164 prefixEnd_1323164 452946077817177565643257 := by
  unfold tailWord_1323164
  simp only [CollatzResearch.WordTrace]
  refine ⟨24129877889205140632624273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32173170518940187510165697 24129877889205140632624273)
  ·
    refine ⟨18097408416903855474468205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24129877889205140632624273 18097408416903855474468205)
    ·
      refine ⟨6786528156338945802925577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18097408416903855474468205 6786528156338945802925577)
      ·
        refine ⟨5089896117254209352194183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6786528156338945802925577 5089896117254209352194183)
        ·
          refine ⟨7634844175881314028291275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5089896117254209352194183 7634844175881314028291275)
          ·
            refine ⟨11452266263821971042436913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7634844175881314028291275 11452266263821971042436913)
            ·
              refine ⟨8589199697866478281827685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11452266263821971042436913 8589199697866478281827685)
              ·
                refine ⟨1610474943349964677842691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8589199697866478281827685 1610474943349964677842691)
                ·
                  refine ⟨2415712415024947016764037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610474943349964677842691 2415712415024947016764037)
                  ·
                    refine ⟨452946077817177565643257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415712415024947016764037 452946077817177565643257)
                    ·
                      rfl

theorem cell22_1323164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1323164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323164 prefixEnd_1323164 := by exact prefixLift 1323164
  have htrace : WordTrace (prefixWord ++ tailWord_1323164) baseStart_1323164 baseEnd_1323164 := by
    simpa [prefixWord, tailWord_1323164, baseEnd_1323164] using wordTrace_append hprefix tailTrace_1323164
  have hstable : (prefixWord ++ tailWord_1323164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323164).length < 2 ^ (prefixWord ++ tailWord_1323164).sum := by decide
  have hdescent : baseEnd_1323164 < baseStart_1323164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323181 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1323181 : Nat := 118140960795 + 1323181 * 2 ^ 59
def prefixEnd_1323181 : Nat := 4983230072969 + 3 ^ 40 * 1323181 * 2
def baseEnd_1323181 : Nat := 452951897264595187968205

theorem tailTrace_1323181 : CollatzResearch.WordTrace tailWord_1323181 prefixEnd_1323181 452951897264595187968205 := by
  unfold tailWord_1323181
  simp only [CollatzResearch.WordTrace]
  refine ⟨48260375819348693168617397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32173583879565795445744931 48260375819348693168617397)
  ·
    refine ⟨4524410233063939984557881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48260375819348693168617397 4524410233063939984557881)
    ·
      refine ⟨3393307674797954988418411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4524410233063939984557881 3393307674797954988418411)
      ·
        refine ⟨5089961512196932482627617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393307674797954988418411 5089961512196932482627617)
        ·
          refine ⟨3817471134147699361970713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5089961512196932482627617 3817471134147699361970713)
          ·
            refine ⟨2863103350610774521478035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3817471134147699361970713 2863103350610774521478035)
            ·
              refine ⟨4294655025916161782217053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863103350610774521478035 4294655025916161782217053)
              ·
                refine ⟨1610495634718560668331395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4294655025916161782217053 1610495634718560668331395)
                ·
                  refine ⟨2415743452077841002497093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610495634718560668331395 2415743452077841002497093)
                  ·
                    refine ⟨452951897264595187968205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415743452077841002497093 452951897264595187968205)
                    ·
                      rfl

theorem cell22_1323181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1323181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323181 prefixEnd_1323181 := by exact prefixLift 1323181
  have htrace : WordTrace (prefixWord ++ tailWord_1323181) baseStart_1323181 baseEnd_1323181 := by
    simpa [prefixWord, tailWord_1323181, baseEnd_1323181] using wordTrace_append hprefix tailTrace_1323181
  have hstable : (prefixWord ++ tailWord_1323181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323181).length < 2 ^ (prefixWord ++ tailWord_1323181).sum := by decide
  have hdescent : baseEnd_1323181 < baseStart_1323181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323192 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1323192 : Nat := 118140960795 + 1323192 * 2 ^ 59
def prefixEnd_1323192 : Nat := 4983230072969 + 3 ^ 40 * 1323192 * 2
def baseEnd_1323192 : Nat := 452955662789394825943171

theorem tailTrace_1323192 : CollatzResearch.WordTrace tailWord_1323192 prefixEnd_1323192 452955662789394825943171 := by
  unfold tailWord_1323192
  simp only [CollatzResearch.WordTrace]
  refine ⟨24130388511154421023633915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32173851348205894698178553 24130388511154421023633915)
  ·
    refine ⟨36195582766731631535450873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24130388511154421023633915 36195582766731631535450873)
    ·
      refine ⟨27146687075048723651588155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36195582766731631535450873 27146687075048723651588155)
      ·
        refine ⟨40720030612573085477382233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27146687075048723651588155 40720030612573085477382233)
        ·
          refine ⟨30540022959429814108036675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40720030612573085477382233 30540022959429814108036675)
          ·
            refine ⟨45810034439144721162055013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30540022959429814108036675 45810034439144721162055013)
            ·
              refine ⟨8589381457339635217885315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45810034439144721162055013 8589381457339635217885315)
              ·
                refine ⟨12884072186009452826827973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8589381457339635217885315 12884072186009452826827973)
                ·
                  refine ⟨2415763534876772405030245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12884072186009452826827973 2415763534876772405030245)
                  ·
                    refine ⟨452955662789394825943171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415763534876772405030245 452955662789394825943171)
                    ·
                      rfl

theorem cell22_1323192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1323192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323192 prefixEnd_1323192 := by exact prefixLift 1323192
  have htrace : WordTrace (prefixWord ++ tailWord_1323192) baseStart_1323192 baseEnd_1323192 := by
    simpa [prefixWord, tailWord_1323192, baseEnd_1323192] using wordTrace_append hprefix tailTrace_1323192
  have hstable : (prefixWord ++ tailWord_1323192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323192).length < 2 ^ (prefixWord ++ tailWord_1323192).sum := by decide
  have hdescent : baseEnd_1323192 < baseStart_1323192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323211 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 2, 3]
def baseStart_1323211 : Nat := 118140960795 + 1323211 * 2 ^ 59
def prefixEnd_1323211 : Nat := 4983230072969 + 3 ^ 40 * 1323211 * 2
def baseEnd_1323211 : Nat := 452962166877685109718113

theorem tailTrace_1323211 : CollatzResearch.WordTrace tailWord_1323211 prefixEnd_1323211 452962166877685109718113 := by
  unfold tailWord_1323211
  simp only [CollatzResearch.WordTrace]
  refine ⟨48261470009240008292209487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32174313339493338861472991 48261470009240008292209487)
  ·
    refine ⟨72392205013860012438314231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48261470009240008292209487 72392205013860012438314231)
    ·
      refine ⟨108588307520790018657471347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72392205013860012438314231 108588307520790018657471347)
      ·
        refine ⟨162882461281185027986207021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108588307520790018657471347 162882461281185027986207021)
        ·
          refine ⟨61080922980444385494827633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162882461281185027986207021 61080922980444385494827633)
          ·
            refine ⟨45810692235333289121120725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61080922980444385494827633 45810692235333289121120725)
            ·
              refine ⟨1073688099265623963776267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45810692235333289121120725 1073688099265623963776267)
              ·
                refine ⟨1610532148898435945664401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073688099265623963776267 1610532148898435945664401)
                ·
                  refine ⟨1207899111673826959248301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610532148898435945664401 1207899111673826959248301)
                  ·
                    refine ⟨452962166877685109718113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1207899111673826959248301 452962166877685109718113)
                    ·
                      rfl

theorem cell22_1323211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 2, 3].length) (baseStart_1323211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323211 prefixEnd_1323211 := by exact prefixLift 1323211
  have htrace : WordTrace (prefixWord ++ tailWord_1323211) baseStart_1323211 baseEnd_1323211 := by
    simpa [prefixWord, tailWord_1323211, baseEnd_1323211] using wordTrace_append hprefix tailTrace_1323211
  have hstable : (prefixWord ++ tailWord_1323211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323211).length < 2 ^ (prefixWord ++ tailWord_1323211).sum := by decide
  have hdescent : baseEnd_1323211 < baseStart_1323211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323224 : List Nat := [2, 1, 2, 2, 4, 1, 4, 6]
def baseStart_1323224 : Nat := 118140960795 + 1323224 * 2 ^ 59
def prefixEnd_1323224 : Nat := 4983230072969 + 3 ^ 40 * 1323224 * 2
def baseEnd_1323224 : Nat := 50329624115928601015897

theorem tailTrace_1323224 : CollatzResearch.WordTrace tailWord_1323224 prefixEnd_1323224 50329624115928601015897 := by
  unfold tailWord_1323224
  simp only [CollatzResearch.WordTrace]
  refine ⟨24130972079096455756216363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32174629438795274341621817 24130972079096455756216363)
  ·
    refine ⟨36196458118644683634324545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24130972079096455756216363 36196458118644683634324545)
    ·
      refine ⟨27147343588983512725743409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36196458118644683634324545 27147343588983512725743409)
      ·
        refine ⟨20360507691737634544307557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27147343588983512725743409 20360507691737634544307557)
        ·
          refine ⟨3817595192200806477057667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20360507691737634544307557 3817595192200806477057667)
          ·
            refine ⟨5726392788301209715586501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817595192200806477057667 5726392788301209715586501)
            ·
              refine ⟨1073698647806476821672469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5726392788301209715586501 1073698647806476821672469)
              ·
                refine ⟨50329624115928601015897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1073698647806476821672469 50329624115928601015897)
                ·
                  rfl

theorem cell22_1323224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 6].length) (baseStart_1323224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323224 prefixEnd_1323224 := by exact prefixLift 1323224
  have htrace : WordTrace (prefixWord ++ tailWord_1323224) baseStart_1323224 baseEnd_1323224 := by
    simpa [prefixWord, tailWord_1323224, baseEnd_1323224] using wordTrace_append hprefix tailTrace_1323224
  have hstable : (prefixWord ++ tailWord_1323224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323224).length < 2 ^ (prefixWord ++ tailWord_1323224).sum := by decide
  have hdescent : baseEnd_1323224 < baseStart_1323224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323256 : List Nat := [2, 1, 2, 1, 1, 2, 1, 8, 1, 3]
def baseStart_1323256 : Nat := 118140960795 + 1323256 * 2 ^ 59
def prefixEnd_1323256 : Nat := 4983230072969 + 3 ^ 40 * 1323256 * 2
def baseEnd_1323256 : Nat := 452977571297319992342975

theorem tailTrace_1323256 : CollatzResearch.WordTrace tailWord_1323256 prefixEnd_1323256 452977571297319992342975 := by
  unfold tailWord_1323256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24131555647038490488798811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32175407529384653985065081 24131555647038490488798811)
  ·
    refine ⟨36197333470557735733198217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24131555647038490488798811 36197333470557735733198217)
    ·
      refine ⟨27148000102918301799898663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36197333470557735733198217 27148000102918301799898663)
      ·
        refine ⟨40722000154377452699847995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27148000102918301799898663 40722000154377452699847995)
        ·
          refine ⟨61083000231566179049771993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40722000154377452699847995 61083000231566179049771993)
          ·
            refine ⟨45812250173674634287328995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61083000231566179049771993 45812250173674634287328995)
            ·
              refine ⟨68718375260511951430993493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45812250173674634287328995 68718375260511951430993493)
              ·
                refine ⟨805293460084124430831955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 68718375260511951430993493 805293460084124430831955)
                ·
                  refine ⟨1207940190126186646247933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805293460084124430831955 1207940190126186646247933)
                  ·
                    refine ⟨452977571297319992342975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1207940190126186646247933 452977571297319992342975)
                    ·
                      rfl

theorem cell22_1323256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_1323256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323256 prefixEnd_1323256 := by exact prefixLift 1323256
  have htrace : WordTrace (prefixWord ++ tailWord_1323256) baseStart_1323256 baseEnd_1323256 := by
    simpa [prefixWord, tailWord_1323256, baseEnd_1323256] using wordTrace_append hprefix tailTrace_1323256
  have hstable : (prefixWord ++ tailWord_1323256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323256).length < 2 ^ (prefixWord ++ tailWord_1323256).sum := by decide
  have hdescent : baseEnd_1323256 < baseStart_1323256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323267 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 1, 7]
def baseStart_1323267 : Nat := 118140960795 + 1323267 * 2 ^ 59
def prefixEnd_1323267 : Nat := 4983230072969 + 3 ^ 40 * 1323267 * 2
def baseEnd_1323267 : Nat := 452981336822119630317941

theorem tailTrace_1323267 : CollatzResearch.WordTrace tailWord_1323267 prefixEnd_1323267 452981336822119630317941 := by
  unfold tailWord_1323267
  simp only [CollatzResearch.WordTrace]
  refine ⟨48263512497037129856248055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32175674998024753237498703 48263512497037129856248055)
  ·
    refine ⟨72395268745555694784372083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48263512497037129856248055 72395268745555694784372083)
    ·
      refine ⟨108592903118333542176558125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72395268745555694784372083 108592903118333542176558125)
      ·
        refine ⟨40722338669375078316209297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108592903118333542176558125 40722338669375078316209297)
        ·
          refine ⟨30541754002031308737156973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40722338669375078316209297 30541754002031308737156973)
          ·
            refine ⟨11453157750761740776433865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30541754002031308737156973 11453157750761740776433865)
            ·
              refine ⟨8589868313071305582325399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11453157750761740776433865 8589868313071305582325399)
              ·
                refine ⟨12884802469606958373488099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8589868313071305582325399 12884802469606958373488099)
                ·
                  refine ⟨19327203704410437560232149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12884802469606958373488099 19327203704410437560232149)
                  ·
                    refine ⟨452981336822119630317941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19327203704410437560232149 452981336822119630317941)
                    ·
                      rfl

theorem cell22_1323267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_1323267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323267 prefixEnd_1323267 := by exact prefixLift 1323267
  have htrace : WordTrace (prefixWord ++ tailWord_1323267) baseStart_1323267 baseEnd_1323267 := by
    simpa [prefixWord, tailWord_1323267, baseEnd_1323267] using wordTrace_append hprefix tailTrace_1323267
  have hstable : (prefixWord ++ tailWord_1323267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323267).length < 2 ^ (prefixWord ++ tailWord_1323267).sum := by decide
  have hdescent : baseEnd_1323267 < baseStart_1323267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323316 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1323316 : Nat := 118140960795 + 1323316 * 2 ^ 59
def prefixEnd_1323316 : Nat := 4983230072969 + 3 ^ 40 * 1323316 * 2
def baseEnd_1323316 : Nat := 452998110523499835842791

theorem tailTrace_1323316 : CollatzResearch.WordTrace tailWord_1323316 prefixEnd_1323316 452998110523499835842791 := by
  unfold tailWord_1323316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24132649836929805612390901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32176866449239740816521201 24132649836929805612390901)
  ·
    refine ⟨2262435922212169276161647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24132649836929805612390901 2262435922212169276161647)
    ·
      refine ⟨3393653883318253914242471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262435922212169276161647 3393653883318253914242471)
      ·
        refine ⟨5090480824977380871363707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3393653883318253914242471 5090480824977380871363707)
        ·
          refine ⟨7635721237466071307045561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5090480824977380871363707 7635721237466071307045561)
          ·
            refine ⟨5726790928099553480284171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7635721237466071307045561 5726790928099553480284171)
            ·
              refine ⟨8590186392149330220426257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726790928099553480284171 8590186392149330220426257)
              ·
                refine ⟨6442639794111997665319693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8590186392149330220426257 6442639794111997665319693)
                ·
                  refine ⟨2415989922791999124494885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6442639794111997665319693 2415989922791999124494885)
                  ·
                    refine ⟨452998110523499835842791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415989922791999124494885 452998110523499835842791)
                    ·
                      rfl

theorem cell22_1323316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1323316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323316 prefixEnd_1323316 := by exact prefixLift 1323316
  have htrace : WordTrace (prefixWord ++ tailWord_1323316) baseStart_1323316 baseEnd_1323316 := by
    simpa [prefixWord, tailWord_1323316, baseEnd_1323316] using wordTrace_append hprefix tailTrace_1323316
  have hstable : (prefixWord ++ tailWord_1323316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323316).length < 2 ^ (prefixWord ++ tailWord_1323316).sum := by decide
  have hdescent : baseEnd_1323316 < baseStart_1323316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323344 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_1323344 : Nat := 118140960795 + 1323344 * 2 ^ 59
def prefixEnd_1323344 : Nat := 4983230072969 + 3 ^ 40 * 1323344 * 2
def baseEnd_1323344 : Nat := 453007695495717096142705

theorem tailTrace_1323344 : CollatzResearch.WordTrace tailWord_1323344 prefixEnd_1323344 453007695495717096142705 := by
  unfold tailWord_1323344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24133160458879086003400543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32177547278505448004534057 24133160458879086003400543)
  ·
    refine ⟨36199740688318629005100815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24133160458879086003400543 36199740688318629005100815)
    ·
      refine ⟨54299611032477943507651223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36199740688318629005100815 54299611032477943507651223)
      ·
        refine ⟨81449416548716915261476835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54299611032477943507651223 81449416548716915261476835)
        ·
          refine ⟨122174124823075372892215253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81449416548716915261476835 122174124823075372892215253)
          ·
            refine ⟨2863456050540829052161295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 122174124823075372892215253 2863456050540829052161295)
            ·
              refine ⟨4295184075811243578241943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863456050540829052161295 4295184075811243578241943)
              ·
                refine ⟨6442776113716865367362915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4295184075811243578241943 6442776113716865367362915)
                ·
                  refine ⟨9664164170575298051044373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6442776113716865367362915 9664164170575298051044373)
                  ·
                    refine ⟨453007695495717096142705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9664164170575298051044373 453007695495717096142705)
                    ·
                      rfl

theorem cell22_1323344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_1323344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323344 prefixEnd_1323344 := by exact prefixLift 1323344
  have htrace : WordTrace (prefixWord ++ tailWord_1323344) baseStart_1323344 baseEnd_1323344 := by
    simpa [prefixWord, tailWord_1323344, baseEnd_1323344] using wordTrace_append hprefix tailTrace_1323344
  have hstable : (prefixWord ++ tailWord_1323344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323344).length < 2 ^ (prefixWord ++ tailWord_1323344).sum := by decide
  have hdescent : baseEnd_1323344 < baseStart_1323344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323348 : List Nat := [2, 4, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1323348 : Nat := 118140960795 + 1323348 * 2 ^ 59
def prefixEnd_1323348 : Nat := 4983230072969 + 3 ^ 40 * 1323348 * 2
def baseEnd_1323348 : Nat := 151003021592487473014231

theorem tailTrace_1323348 : CollatzResearch.WordTrace tailWord_1323348 prefixEnd_1323348 151003021592487473014231 := by
  unfold tailWord_1323348
  simp only [CollatzResearch.WordTrace]
  refine ⟨24133233404871840344973349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32177644539829120459964465 24133233404871840344973349)
  ·
    refine ⟨4524981263413470064682503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24133233404871840344973349 4524981263413470064682503)
    ·
      refine ⟨6787471895120205097023755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4524981263413470064682503 6787471895120205097023755)
      ·
        refine ⟨10181207842680307645535633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6787471895120205097023755 10181207842680307645535633)
        ·
          refine ⟨7635905882010230734151725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10181207842680307645535633 7635905882010230734151725)
          ·
            refine ⟨2863464705753836525306897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7635905882010230734151725 2863464705753836525306897)
            ·
              refine ⟨2147598529315377393980173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863464705753836525306897 2147598529315377393980173)
              ·
                refine ⟨805349448493266522742565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2147598529315377393980173 805349448493266522742565)
                ·
                  refine ⟨151003021592487473014231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805349448493266522742565 151003021592487473014231)
                  ·
                    rfl

theorem cell22_1323348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1323348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323348 prefixEnd_1323348 := by exact prefixLift 1323348
  have htrace : WordTrace (prefixWord ++ tailWord_1323348) baseStart_1323348 baseEnd_1323348 := by
    simpa [prefixWord, tailWord_1323348, baseEnd_1323348] using wordTrace_append hprefix tailTrace_1323348
  have hstable : (prefixWord ++ tailWord_1323348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323348).length < 2 ^ (prefixWord ++ tailWord_1323348).sum := by decide
  have hdescent : baseEnd_1323348 < baseStart_1323348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323393 : List Nat := [1, 2, 4, 3, 1, 3, 2, 6]
def baseStart_1323393 : Nat := 118140960795 + 1323393 * 2 ^ 59
def prefixEnd_1323393 : Nat := 4983230072969 + 3 ^ 40 * 1323393 * 2
def baseEnd_1323393 : Nat := 50336052133010811296395

theorem tailTrace_1323393 : CollatzResearch.WordTrace tailWord_1323393 prefixEnd_1323393 50336052133010811296395 := by
  unfold tailWord_1323393
  simp only [CollatzResearch.WordTrace]
  refine ⟨48268108094580653375334833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32178738729720435583556555 48268108094580653375334833)
  ·
    refine ⟨36201081070935490031501125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48268108094580653375334833 36201081070935490031501125)
    ·
      refine ⟨6787702700800404380906461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36201081070935490031501125 6787702700800404380906461)
      ·
        refine ⟨2545388512800151642839923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6787702700800404380906461 2545388512800151642839923)
        ·
          refine ⟨3818082769200227464259885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2545388512800151642839923 3818082769200227464259885)
          ·
            refine ⟨1431781038450085299097457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3818082769200227464259885 1431781038450085299097457)
            ·
              refine ⟨1073835778837563974323093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431781038450085299097457 1073835778837563974323093)
              ·
                refine ⟨50336052133010811296395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1073835778837563974323093 50336052133010811296395)
                ·
                  rfl

theorem cell22_1323393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 6].length) (baseStart_1323393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323393 prefixEnd_1323393 := by exact prefixLift 1323393
  have htrace : WordTrace (prefixWord ++ tailWord_1323393) baseStart_1323393 baseEnd_1323393 := by
    simpa [prefixWord, tailWord_1323393, baseEnd_1323393] using wordTrace_append hprefix tailTrace_1323393
  have hstable : (prefixWord ++ tailWord_1323393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323393).length < 2 ^ (prefixWord ++ tailWord_1323393).sum := by decide
  have hdescent : baseEnd_1323393 < baseStart_1323393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323404 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 7]
def baseStart_1323404 : Nat := 118140960795 + 1323404 * 2 ^ 59
def prefixEnd_1323404 : Nat := 4983230072969 + 3 ^ 40 * 1323404 * 2
def baseEnd_1323404 : Nat := 151009411573965646547507

theorem tailTrace_1323404 : CollatzResearch.WordTrace tailWord_1323404 prefixEnd_1323404 151009411573965646547507 := by
  unfold tailWord_1323404
  simp only [CollatzResearch.WordTrace]
  refine ⟨24134254648770401126992633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32179006198360534835990177 24134254648770401126992633)
  ·
    refine ⟨18100690986577800845244475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24134254648770401126992633 18100690986577800845244475)
    ·
      refine ⟨27151036479866701267866713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18100690986577800845244475 27151036479866701267866713)
      ·
        refine ⟨20363277359900025950900035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27151036479866701267866713 20363277359900025950900035)
        ·
          refine ⟨30544916039850038926350053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20363277359900025950900035 30544916039850038926350053)
          ·
            refine ⟨5727171757471882298690635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30544916039850038926350053 5727171757471882298690635)
            ·
              refine ⟨8590757636207823448035953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5727171757471882298690635 8590757636207823448035953)
              ·
                refine ⟨6443068227155867586026965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8590757636207823448035953 6443068227155867586026965)
                ·
                  refine ⟨151009411573965646547507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6443068227155867586026965 151009411573965646547507)
                  ·
                    rfl

theorem cell22_1323404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_1323404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323404 prefixEnd_1323404 := by exact prefixLift 1323404
  have htrace : WordTrace (prefixWord ++ tailWord_1323404) baseStart_1323404 baseEnd_1323404 := by
    simpa [prefixWord, tailWord_1323404, baseEnd_1323404] using wordTrace_append hprefix tailTrace_1323404
  have hstable : (prefixWord ++ tailWord_1323404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323404).length < 2 ^ (prefixWord ++ tailWord_1323404).sum := by decide
  have hdescent : baseEnd_1323404 < baseStart_1323404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323479 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 5, 6]
def baseStart_1323479 : Nat := 118140960795 + 1323479 * 2 ^ 59
def prefixEnd_1323479 : Nat := 4983230072969 + 3 ^ 40 * 1323479 * 2
def baseEnd_1323479 : Nat := 453053908754621744017291

theorem tailTrace_1323479 : CollatzResearch.WordTrace tailWord_1323479 prefixEnd_1323479 453053908754621744017291 := by
  unfold tailWord_1323479
  simp only [CollatzResearch.WordTrace]
  refine ⟨48271244772269090062965491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32180829848179393375310327 48271244772269090062965491)
  ·
    refine ⟨72406867158403635094448237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48271244772269090062965491 72406867158403635094448237)
    ·
      refine ⟨27152575184401363160418089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72406867158403635094448237 27152575184401363160418089)
      ·
        refine ⟨20364431388301022370313567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27152575184401363160418089 20364431388301022370313567)
        ·
          refine ⟨30546647082451533555470351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20364431388301022370313567 30546647082451533555470351)
          ·
            refine ⟨45819970623677300333205527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30546647082451533555470351 45819970623677300333205527)
            ·
              refine ⟨68729955935515950499808291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45819970623677300333205527 68729955935515950499808291)
              ·
                refine ⟨103094933903273925749712437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68729955935515950499808291 103094933903273925749712437)
                ·
                  refine ⟨9665150053431930539035541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103094933903273925749712437 9665150053431930539035541)
                  ·
                    refine ⟨453053908754621744017291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9665150053431930539035541 453053908754621744017291)
                    ·
                      rfl

theorem cell22_1323479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_1323479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323479 prefixEnd_1323479 := by exact prefixLift 1323479
  have htrace : WordTrace (prefixWord ++ tailWord_1323479) baseStart_1323479 baseEnd_1323479 := by
    simpa [prefixWord, tailWord_1323479, baseEnd_1323479] using wordTrace_append hprefix tailTrace_1323479
  have hstable : (prefixWord ++ tailWord_1323479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323479).length < 2 ^ (prefixWord ++ tailWord_1323479).sum := by decide
  have hdescent : baseEnd_1323479 < baseStart_1323479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1323498 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1323498 : Nat := 118140960795 + 1323498 * 2 ^ 59
def prefixEnd_1323498 : Nat := 4983230072969 + 3 ^ 40 * 1323498 * 2
def baseEnd_1323498 : Nat := 453060412842912027792233

theorem tailTrace_1323498 : CollatzResearch.WordTrace tailWord_1323498 prefixEnd_1323498 453060412842912027792233 := by
  unfold tailWord_1323498
  simp only [CollatzResearch.WordTrace]
  refine ⟨12067984439800064076976787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32181291839466837538604765 12067984439800064076976787)
  ·
    refine ⟨18101976659700096115465181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12067984439800064076976787 18101976659700096115465181)
    ·
      refine ⟨6788241247387536043299443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18101976659700096115465181 6788241247387536043299443)
      ·
        refine ⟨10182361871081304064949165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6788241247387536043299443 10182361871081304064949165)
        ·
          refine ⟨3818385701655489024355937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10182361871081304064949165 3818385701655489024355937)
          ·
            refine ⟨2863789276241616768266953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3818385701655489024355937 2863789276241616768266953)
            ·
              refine ⟨2147841957181212576200215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863789276241616768266953 2147841957181212576200215)
              ·
                refine ⟨3221762935771818864300323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2147841957181212576200215 3221762935771818864300323)
                ·
                  refine ⟨4832644403657728296450485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221762935771818864300323 4832644403657728296450485)
                  ·
                    refine ⟨453060412842912027792233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4832644403657728296450485 453060412842912027792233)
                    ·
                      rfl

theorem cell22_1323498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1323498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1323498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1323498 prefixEnd_1323498 := by exact prefixLift 1323498
  have htrace : WordTrace (prefixWord ++ tailWord_1323498) baseStart_1323498 baseEnd_1323498 := by
    simpa [prefixWord, tailWord_1323498, baseEnd_1323498] using wordTrace_append hprefix tailTrace_1323498
  have hstable : (prefixWord ++ tailWord_1323498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1323498).length < 2 ^ (prefixWord ++ tailWord_1323498).sum := by decide
  have hdescent : baseEnd_1323498 < baseStart_1323498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1323498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
