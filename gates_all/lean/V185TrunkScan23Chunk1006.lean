import V185TrunkScan23Chunk1005

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5957586 : List Nat := [3, 2, 2, 3, 2, 1, 2, 3, 5]
def baseStart_5957586 : Nat := 118140960795 + 5957586 * 2 ^ 59
def prefixEnd_5957586 : Nat := 4983230072969 + 3 ^ 40 * 5957586 * 2
def baseEnd_5957586 : Nat := 339900573166314794564063

theorem tailTrace_5957586 : CollatzResearch.WordTrace tailWord_5957586 prefixEnd_5957586 339900573166314794564063 := by
  unfold tailWord_5957586
  simp only [CollatzResearch.WordTrace]
  refine ⟨54322753148672717882153153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144860675063127247685741741 54322753148672717882153153)
  ·
    refine ⟨40742064861504538411614865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54322753148672717882153153 40742064861504538411614865)
    ·
      refine ⟨30556548646128403808711149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40742064861504538411614865 30556548646128403808711149)
      ·
        refine ⟨11458705742298151428266681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30556548646128403808711149 11458705742298151428266681)
        ·
          refine ⟨8594029306723613571200011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11458705742298151428266681 8594029306723613571200011)
          ·
            refine ⟨12891043960085420356800017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594029306723613571200011 12891043960085420356800017)
            ·
              refine ⟨9668282970064065267600013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12891043960085420356800017 9668282970064065267600013)
              ·
                refine ⟨3625606113774024475350005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9668282970064065267600013 3625606113774024475350005)
                ·
                  refine ⟨339900573166314794564063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3625606113774024475350005 339900573166314794564063)
                  ·
                    rfl

theorem cell23_5957586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_5957586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957586 prefixEnd_5957586 := by exact prefixLift 5957586
  have htrace : WordTrace (prefixWord ++ tailWord_5957586) baseStart_5957586 baseEnd_5957586 := by
    simpa [prefixWord, tailWord_5957586, baseEnd_5957586] using wordTrace_append hprefix tailTrace_5957586
  have hstable : (prefixWord ++ tailWord_5957586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957586).length < 2 ^ (prefixWord ++ tailWord_5957586).sum := by decide
  have hdescent : baseEnd_5957586 < baseStart_5957586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957615 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_5957615 : Nat := 118140960795 + 5957615 * 2 ^ 59
def prefixEnd_5957615 : Nat := 4983230072969 + 3 ^ 40 * 5957615 * 2
def baseEnd_5957615 : Nat := 3059120049435813537613933

theorem tailTrace_5957615 : CollatzResearch.WordTrace tailWord_5957615 prefixEnd_5957615 3059120049435813537613933 := by
  unfold tailWord_5957615
  simp only [CollatzResearch.WordTrace]
  refine ⟨217292070311585809481418299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144861380207723872987612199 217292070311585809481418299)
  ·
    refine ⟨325938105467378714222127449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217292070311585809481418299 325938105467378714222127449)
    ·
      refine ⟨244453579100534035666595587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325938105467378714222127449 244453579100534035666595587)
      ·
        refine ⟨366680368650801053499893381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244453579100534035666595587 366680368650801053499893381)
        ·
          refine ⟨68752569122025197531230009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366680368650801053499893381 68752569122025197531230009)
          ·
            refine ⟨51564426841518898148422507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68752569122025197531230009 51564426841518898148422507)
            ·
              refine ⟨77346640262278347222633761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51564426841518898148422507 77346640262278347222633761)
              ·
                refine ⟨58009980196708760416975321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77346640262278347222633761 58009980196708760416975321)
                ·
                  refine ⟨43507485147531570312731491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58009980196708760416975321 43507485147531570312731491)
                  ·
                    refine ⟨65261227721297355469097237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43507485147531570312731491 65261227721297355469097237)
                    ·
                      refine ⟨3059120049435813537613933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65261227721297355469097237 3059120049435813537613933)
                      ·
                        rfl

theorem cell23_5957615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_5957615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957615 prefixEnd_5957615 := by exact prefixLift 5957615
  have htrace : WordTrace (prefixWord ++ tailWord_5957615) baseStart_5957615 baseEnd_5957615 := by
    simpa [prefixWord, tailWord_5957615, baseEnd_5957615] using wordTrace_append hprefix tailTrace_5957615
  have hstable : (prefixWord ++ tailWord_5957615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957615).length < 2 ^ (prefixWord ++ tailWord_5957615).sum := by decide
  have hdescent : baseEnd_5957615 < baseStart_5957615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957686 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_5957686 : Nat := 118140960795 + 5957686 * 2 ^ 59
def prefixEnd_5957686 : Nat := 4983230072969 + 3 ^ 40 * 5957686 * 2
def baseEnd_5957686 : Nat := 3059156506562282759826107

theorem tailTrace_5957686 : CollatzResearch.WordTrace tailWord_5957686 prefixEnd_5957686 3059156506562282759826107 := by
  unfold tailWord_5957686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13580916243395536787953307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144863106596219059071501941 13580916243395536787953307)
  ·
    refine ⟨20371374365093305181929961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13580916243395536787953307 20371374365093305181929961)
    ·
      refine ⟨15278530773819978886447471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20371374365093305181929961 15278530773819978886447471)
      ·
        refine ⟨22917796160729968329671207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15278530773819978886447471 22917796160729968329671207)
        ·
          refine ⟨34376694241094952494506811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22917796160729968329671207 34376694241094952494506811)
          ·
            refine ⟨51565041361642428741760217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34376694241094952494506811 51565041361642428741760217)
            ·
              refine ⟨38673781021231821556320163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51565041361642428741760217 38673781021231821556320163)
              ·
                refine ⟨58010671531847732334480245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38673781021231821556320163 58010671531847732334480245)
                ·
                  refine ⟨5438500456110724906357523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58010671531847732334480245 5438500456110724906357523)
                  ·
                    refine ⟨8157750684166087359536285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438500456110724906357523 8157750684166087359536285)
                    ·
                      refine ⟨3059156506562282759826107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8157750684166087359536285 3059156506562282759826107)
                      ·
                        rfl

theorem cell23_5957686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_5957686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957686 prefixEnd_5957686 := by exact prefixLift 5957686
  have htrace : WordTrace (prefixWord ++ tailWord_5957686) baseStart_5957686 baseEnd_5957686 := by
    simpa [prefixWord, tailWord_5957686, baseEnd_5957686] using wordTrace_append hprefix tailTrace_5957686
  have hstable : (prefixWord ++ tailWord_5957686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957686).length < 2 ^ (prefixWord ++ tailWord_5957686).sum := by decide
  have hdescent : baseEnd_5957686 < baseStart_5957686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957689 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 3, 5]
def baseStart_5957689 : Nat := 118140960795 + 5957689 * 2 ^ 59
def prefixEnd_5957689 : Nat := 4983230072969 + 3 ^ 40 * 5957689 * 2
def baseEnd_5957689 : Nat := 1019719349001415416029531

theorem tailTrace_5957689 : CollatzResearch.WordTrace tailWord_5957689 prefixEnd_5957689 1019719349001415416029531 := by
  unfold tailWord_5957689
  simp only [CollatzResearch.WordTrace]
  refine ⟨217294769313317720119612121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144863179542211813413074747 217294769313317720119612121)
  ·
    refine ⟨162971076984988290089709091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217294769313317720119612121 162971076984988290089709091)
    ·
      refine ⟨244456615477482435134563637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162971076984988290089709091 244456615477482435134563637)
      ·
        refine ⟨22917807701013978293865341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244456615477482435134563637 22917807701013978293865341)
        ·
          refine ⟨8594177887880241860199503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22917807701013978293865341 8594177887880241860199503)
          ·
            refine ⟨12891266831820362790299255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594177887880241860199503 12891266831820362790299255)
            ·
              refine ⟨19336900247730544185448883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12891266831820362790299255 19336900247730544185448883)
              ·
                refine ⟨29005350371595816278173325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19336900247730544185448883 29005350371595816278173325)
                ·
                  refine ⟨10877006389348431104314997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29005350371595816278173325 10877006389348431104314997)
                  ·
                    refine ⟨1019719349001415416029531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10877006389348431104314997 1019719349001415416029531)
                    ·
                      rfl

theorem cell23_5957689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_5957689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957689 prefixEnd_5957689 := by exact prefixLift 5957689
  have htrace : WordTrace (prefixWord ++ tailWord_5957689) baseStart_5957689 baseEnd_5957689 := by
    simpa [prefixWord, tailWord_5957689, baseEnd_5957689] using wordTrace_append hprefix tailTrace_5957689
  have hstable : (prefixWord ++ tailWord_5957689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957689).length < 2 ^ (prefixWord ++ tailWord_5957689).sum := by decide
  have hdescent : baseEnd_5957689 < baseStart_5957689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957696 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 2, 3, 2]
def baseStart_5957696 : Nat := 118140960795 + 5957696 * 2 ^ 59
def prefixEnd_5957696 : Nat := 4983230072969 + 3 ^ 40 * 5957696 * 2
def baseEnd_5957696 : Nat := 3059161641368827720701061

theorem tailTrace_5957696 : CollatzResearch.WordTrace tailWord_5957696 prefixEnd_5957696 3059161641368827720701061 := by
  unfold tailWord_5957696
  simp only [CollatzResearch.WordTrace]
  refine ⟨108647512312146180157558471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144863349749528240210077961 108647512312146180157558471)
  ·
    refine ⟨162971268468219270236337707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108647512312146180157558471 162971268468219270236337707)
    ·
      refine ⟨244456902702328905354506561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162971268468219270236337707 244456902702328905354506561)
      ·
        refine ⟨183342677026746679015879921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244456902702328905354506561 183342677026746679015879921)
        ·
          refine ⟨137507007770060009261909941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183342677026746679015879921 137507007770060009261909941)
          ·
            refine ⟨12891281978443125868304057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137507007770060009261909941 12891281978443125868304057)
            ·
              refine ⟨9668461483832344401228043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12891281978443125868304057 9668461483832344401228043)
              ·
                refine ⟨14502692225748516601842065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9668461483832344401228043 14502692225748516601842065)
                ·
                  refine ⟨10877019169311387451381549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14502692225748516601842065 10877019169311387451381549)
                  ·
                    refine ⟨4078882188491770294268081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10877019169311387451381549 4078882188491770294268081)
                    ·
                      refine ⟨3059161641368827720701061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078882188491770294268081 3059161641368827720701061)
                      ·
                        rfl

theorem cell23_5957696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_5957696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957696 prefixEnd_5957696 := by exact prefixLift 5957696
  have htrace : WordTrace (prefixWord ++ tailWord_5957696) baseStart_5957696 baseEnd_5957696 := by
    simpa [prefixWord, tailWord_5957696, baseEnd_5957696] using wordTrace_append hprefix tailTrace_5957696
  have hstable : (prefixWord ++ tailWord_5957696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957696).length < 2 ^ (prefixWord ++ tailWord_5957696).sum := by decide
  have hdescent : baseEnd_5957696 < baseStart_5957696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957719 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 2, 4]
def baseStart_5957719 : Nat := 118140960795 + 5957719 * 2 ^ 59
def prefixEnd_5957719 : Nat := 4983230072969 + 3 ^ 40 * 5957719 * 2
def baseEnd_5957719 : Nat := 1019724483807960376904485

theorem tailTrace_5957719 : CollatzResearch.WordTrace tailWord_5957719 prefixEnd_5957719 1019724483807960376904485 := by
  unfold tailWord_5957719
  simp only [CollatzResearch.WordTrace]
  refine ⟨217295863503209035243204211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144863909002139356828802807 217295863503209035243204211)
  ·
    refine ⟨325943795254813552864806317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217295863503209035243204211 325943795254813552864806317)
    ·
      refine ⟨122228923220555082324302369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325943795254813552864806317 122228923220555082324302369)
      ·
        refine ⟨91671692415416311743226777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122228923220555082324302369 91671692415416311743226777)
        ·
          refine ⟨68753769311562233807420083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91671692415416311743226777 68753769311562233807420083)
          ·
            refine ⟨103130653967343350711130125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68753769311562233807420083 103130653967343350711130125)
            ·
              refine ⟨38673995237753756516673797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103130653967343350711130125 38673995237753756516673797)
              ·
                refine ⟨7251374107078829346876337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38673995237753756516673797 7251374107078829346876337)
                ·
                  refine ⟨5438530580309122010157253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7251374107078829346876337 5438530580309122010157253)
                  ·
                    refine ⟨1019724483807960376904485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5438530580309122010157253 1019724483807960376904485)
                    ·
                      rfl

theorem cell23_5957719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_5957719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957719 prefixEnd_5957719 := by exact prefixLift 5957719
  have htrace : WordTrace (prefixWord ++ tailWord_5957719) baseStart_5957719 baseEnd_5957719 := by
    simpa [prefixWord, tailWord_5957719, baseEnd_5957719] using wordTrace_append hprefix tailTrace_5957719
  have hstable : (prefixWord ++ tailWord_5957719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957719).length < 2 ^ (prefixWord ++ tailWord_5957719).sum := by decide
  have hdescent : baseEnd_5957719 < baseStart_5957719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957720 : List Nat := [2, 1, 2, 2, 1, 6, 2, 2, 1, 1, 3]
def baseStart_5957720 : Nat := 118140960795 + 5957720 * 2 ^ 59
def prefixEnd_5957720 : Nat := 4983230072969 + 3 ^ 40 * 5957720 * 2
def baseEnd_5957720 : Nat := 3059173964904535626800951

theorem tailTrace_5957720 : CollatzResearch.WordTrace tailWord_5957720 prefixEnd_5957720 3059173964904535626800951 := by
  unfold tailWord_5957720
  simp only [CollatzResearch.WordTrace]
  refine ⟨108647949988102706206995307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144863933317470274942660409 108647949988102706206995307)
  ·
    refine ⟨162971924982154059310492961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108647949988102706206995307 162971924982154059310492961)
    ·
      refine ⟨122228943736615544482869721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162971924982154059310492961 122228943736615544482869721)
      ·
        refine ⟨91671707802461658362152291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122228943736615544482869721 91671707802461658362152291)
        ·
          refine ⟨137507561703692487543228437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91671707802461658362152291 137507561703692487543228437)
          ·
            refine ⟨6445666954860585353588833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137507561703692487543228437 6445666954860585353588833)
            ·
              refine ⟨4834250216145439015191625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6445666954860585353588833 4834250216145439015191625)
              ·
                refine ⟨3625687662109079261393719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4834250216145439015191625 3625687662109079261393719)
                ·
                  refine ⟨5438531493163618892090579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625687662109079261393719 5438531493163618892090579)
                  ·
                    refine ⟨8157797239745428338135869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438531493163618892090579 8157797239745428338135869)
                    ·
                      refine ⟨3059173964904535626800951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8157797239745428338135869 3059173964904535626800951)
                      ·
                        rfl

theorem cell23_5957720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_5957720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957720 prefixEnd_5957720 := by exact prefixLift 5957720
  have htrace : WordTrace (prefixWord ++ tailWord_5957720) baseStart_5957720 baseEnd_5957720 := by
    simpa [prefixWord, tailWord_5957720, baseEnd_5957720] using wordTrace_append hprefix tailTrace_5957720
  have hstable : (prefixWord ++ tailWord_5957720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957720).length < 2 ^ (prefixWord ++ tailWord_5957720).sum := by decide
  have hdescent : baseEnd_5957720 < baseStart_5957720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957722 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_5957722 : Nat := 118140960795 + 5957722 * 2 ^ 59
def prefixEnd_5957722 : Nat := 4983230072969 + 3 ^ 40 * 5957722 * 2
def baseEnd_5957722 : Nat := 3059174991865844618975941

theorem tailTrace_5957722 : CollatzResearch.WordTrace tailWord_5957722 prefixEnd_5957722 3059174991865844618975941 := by
  unfold tailWord_5957722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54323993230549541688890855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144863981948132111170375613 54323993230549541688890855)
  ·
    refine ⟨81485989845824312533336283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54323993230549541688890855 81485989845824312533336283)
    ·
      refine ⟨122228984768736468800004425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81485989845824312533336283 122228984768736468800004425)
      ·
        refine ⟨91671738576552351600003319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122228984768736468800004425 91671738576552351600003319)
        ·
          refine ⟨137507607864828527400004979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91671738576552351600003319 137507607864828527400004979)
          ·
            refine ⟨206261411797242791100007469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137507607864828527400004979 206261411797242791100007469)
            ·
              refine ⟨77348029423966046662502801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206261411797242791100007469 77348029423966046662502801)
              ·
                refine ⟨58011022067974534996877101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77348029423966046662502801 58011022067974534996877101)
                ·
                  refine ⟨21754133275490450623828913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58011022067974534996877101 21754133275490450623828913)
                  ·
                    refine ⟨16315599956617837967871685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21754133275490450623828913 16315599956617837967871685)
                    ·
                      refine ⟨3059174991865844618975941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16315599956617837967871685 3059174991865844618975941)
                      ·
                        rfl

theorem cell23_5957722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_5957722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957722 prefixEnd_5957722 := by exact prefixLift 5957722
  have htrace : WordTrace (prefixWord ++ tailWord_5957722) baseStart_5957722 baseEnd_5957722 := by
    simpa [prefixWord, tailWord_5957722, baseEnd_5957722] using wordTrace_append hprefix tailTrace_5957722
  have hstable : (prefixWord ++ tailWord_5957722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957722).length < 2 ^ (prefixWord ++ tailWord_5957722).sum := by decide
  have hdescent : baseEnd_5957722 < baseStart_5957722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957732 : List Nat := [2, 3, 1, 1, 2, 1, 5, 8]
def baseStart_5957732 : Nat := 118140960795 + 5957732 * 2 ^ 59
def prefixEnd_5957732 : Nat := 4983230072969 + 3 ^ 40 * 5957732 * 2
def baseEnd_5957732 : Nat := 113302967654532947401885

theorem tailTrace_5957732 : CollatzResearch.WordTrace tailWord_5957732 prefixEnd_5957732 113302967654532947401885 := by
  unfold tailWord_5957732
  simp only [CollatzResearch.WordTrace]
  refine ⟨108648168826080969231713725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144864225101441292308951633 108648168826080969231713725)
  ·
    refine ⟨40743063309780363461892647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108648168826080969231713725 40743063309780363461892647)
    ·
      refine ⟨61114594964670545192838971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40743063309780363461892647 61114594964670545192838971)
      ·
        refine ⟨91671892447005817789258457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61114594964670545192838971 91671892447005817789258457)
        ·
          refine ⟨68753919335254363341943843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91671892447005817789258457 68753919335254363341943843)
          ·
            refine ⟨103130879002881545012915765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68753919335254363341943843 103130879002881545012915765)
            ·
              refine ⟨9668519906520144844960853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103130879002881545012915765 9668519906520144844960853)
              ·
                refine ⟨113302967654532947401885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9668519906520144844960853 113302967654532947401885)
                ·
                  rfl

theorem cell23_5957732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 8].length) (baseStart_5957732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957732 prefixEnd_5957732 := by exact prefixLift 5957732
  have htrace : WordTrace (prefixWord ++ tailWord_5957732) baseStart_5957732 baseEnd_5957732 := by
    simpa [prefixWord, tailWord_5957732, baseEnd_5957732] using wordTrace_append hprefix tailTrace_5957732
  have hstable : (prefixWord ++ tailWord_5957732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957732).length < 2 ^ (prefixWord ++ tailWord_5957732).sum := by decide
  have hdescent : baseEnd_5957732 < baseStart_5957732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957763 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 1, 2, 3]
def baseStart_5957763 : Nat := 118140960795 + 5957763 * 2 ^ 59
def prefixEnd_5957763 : Nat := 4983230072969 + 3 ^ 40 * 5957763 * 2
def baseEnd_5957763 : Nat := 3059196044572678958563253

theorem tailTrace_5957763 : CollatzResearch.WordTrace tailWord_5957763 prefixEnd_5957763 3059196044572678958563253 := by
  unfold tailWord_5957763
  simp only [CollatzResearch.WordTrace]
  refine ⟨217297468315049630757805943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144864978876699753838537295 217297468315049630757805943)
  ·
    refine ⟨325946202472574446136708915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217297468315049630757805943 325946202472574446136708915)
    ·
      refine ⟨488919303708861669205063373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325946202472574446136708915 488919303708861669205063373)
      ·
        refine ⟨183344738890823125951898765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488919303708861669205063373 183344738890823125951898765)
        ·
          refine ⟨68754277084058672231962037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183344738890823125951898765 68754277084058672231962037)
          ·
            refine ⟨6445713476630500521746441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68754277084058672231962037 6445713476630500521746441)
            ·
              refine ⟨4834285107472875391309831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6445713476630500521746441 4834285107472875391309831)
              ·
                refine ⟨7251427661209313086964747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4834285107472875391309831 7251427661209313086964747)
                ·
                  refine ⟨10877141491813969630447121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7251427661209313086964747 10877141491813969630447121)
                  ·
                    refine ⟨8157856118860477222835341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10877141491813969630447121 8157856118860477222835341)
                    ·
                      refine ⟨3059196044572678958563253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8157856118860477222835341 3059196044572678958563253)
                      ·
                        rfl

theorem cell23_5957763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_5957763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957763 prefixEnd_5957763 := by exact prefixLift 5957763
  have htrace : WordTrace (prefixWord ++ tailWord_5957763) baseStart_5957763 baseEnd_5957763 := by
    simpa [prefixWord, tailWord_5957763, baseEnd_5957763] using wordTrace_append hprefix tailTrace_5957763
  have hstable : (prefixWord ++ tailWord_5957763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957763).length < 2 ^ (prefixWord ++ tailWord_5957763).sum := by decide
  have hdescent : baseEnd_5957763 < baseStart_5957763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957790 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_5957790 : Nat := 118140960795 + 5957790 * 2 ^ 59
def prefixEnd_5957790 : Nat := 4983230072969 + 3 ^ 40 * 5957790 * 2
def baseEnd_5957790 : Nat := 3059209908550350352925629

theorem tailTrace_5957790 : CollatzResearch.WordTrace tailWord_5957790 prefixEnd_5957790 3059209908550350352925629 := by
  unfold tailWord_5957790
  simp only [CollatzResearch.WordTrace]
  refine ⟨27162306635743976796129853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144865635390634542912692549 27162306635743976796129853)
  ·
    refine ⟨10185864988403991298548695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27162306635743976796129853 10185864988403991298548695)
    ·
      refine ⟨15278797482605986947823043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10185864988403991298548695 15278797482605986947823043)
      ·
        refine ⟨22918196223908980421734565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15278797482605986947823043 22918196223908980421734565)
        ·
          refine ⟨4297161791982933829075231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22918196223908980421734565 4297161791982933829075231)
          ·
            refine ⟨6445742687974400743612847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297161791982933829075231 6445742687974400743612847)
            ·
              refine ⟨9668614031961601115419271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445742687974400743612847 9668614031961601115419271)
              ·
                refine ⟨14502921047942401673128907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9668614031961601115419271 14502921047942401673128907)
                ·
                  refine ⟨21754381571913602509693361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14502921047942401673128907 21754381571913602509693361)
                  ·
                    refine ⟨16315786178935201882270021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21754381571913602509693361 16315786178935201882270021)
                    ·
                      refine ⟨3059209908550350352925629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16315786178935201882270021 3059209908550350352925629)
                      ·
                        rfl

theorem cell23_5957790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_5957790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957790 prefixEnd_5957790 := by exact prefixLift 5957790
  have htrace : WordTrace (prefixWord ++ tailWord_5957790) baseStart_5957790 baseEnd_5957790 := by
    simpa [prefixWord, tailWord_5957790, baseEnd_5957790] using wordTrace_append hprefix tailTrace_5957790
  have hstable : (prefixWord ++ tailWord_5957790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957790).length < 2 ^ (prefixWord ++ tailWord_5957790).sum := by decide
  have hdescent : baseEnd_5957790 < baseStart_5957790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957816 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 6, 2, 2]
def baseStart_5957816 : Nat := 118140960795 + 5957816 * 2 ^ 59
def prefixEnd_5957816 : Nat := 4983230072969 + 3 ^ 40 * 5957816 * 2
def baseEnd_5957816 : Nat := 3059223259047367251200509

theorem tailTrace_5957816 : CollatzResearch.WordTrace tailWord_5957816 prefixEnd_5957816 3059223259047367251200509 := by
  unfold tailWord_5957816
  simp only [CollatzResearch.WordTrace]
  refine ⟨108649700691928810404742651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144866267589238413872990201 108649700691928810404742651)
  ·
    refine ⟨162974551037893215607113977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108649700691928810404742651 162974551037893215607113977)
    ·
      refine ⟨122230913278419911705335483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162974551037893215607113977 122230913278419911705335483)
      ·
        refine ⟨183346369917629867558003225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122230913278419911705335483 183346369917629867558003225)
        ·
          refine ⟨137509777438222400668502419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183346369917629867558003225 137509777438222400668502419)
          ·
            refine ⟨206264666157333601002753629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137509777438222400668502419 206264666157333601002753629)
            ·
              refine ⟨77349249809000100376032611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206264666157333601002753629 77349249809000100376032611)
              ·
                refine ⟨116023874713500150564048917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77349249809000100376032611 116023874713500150564048917)
                ·
                  refine ⟨5438619127195319557689793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116023874713500150564048917 5438619127195319557689793)
                  ·
                    refine ⟨4078964345396489668267345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5438619127195319557689793 4078964345396489668267345)
                    ·
                      refine ⟨3059223259047367251200509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078964345396489668267345 3059223259047367251200509)
                      ·
                        rfl

theorem cell23_5957816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_5957816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957816 prefixEnd_5957816 := by exact prefixLift 5957816
  have htrace : WordTrace (prefixWord ++ tailWord_5957816) baseStart_5957816 baseEnd_5957816 := by
    simpa [prefixWord, tailWord_5957816, baseEnd_5957816] using wordTrace_append hprefix tailTrace_5957816
  have hstable : (prefixWord ++ tailWord_5957816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957816).length < 2 ^ (prefixWord ++ tailWord_5957816).sum := by decide
  have hdescent : baseEnd_5957816 < baseStart_5957816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957832 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_5957832 : Nat := 118140960795 + 5957832 * 2 ^ 59
def prefixEnd_5957832 : Nat := 4983230072969 + 3 ^ 40 * 5957832 * 2
def baseEnd_5957832 : Nat := 3059231474737839188600435

theorem tailTrace_5957832 : CollatzResearch.WordTrace tailWord_5957832 prefixEnd_5957832 3059231474737839188600435 := by
  unfold tailWord_5957832
  simp only [CollatzResearch.WordTrace]
  refine ⟨108649992475899827771033875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144866656634533103694711833 108649992475899827771033875)
  ·
    refine ⟨162974988713849741656550813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108649992475899827771033875 162974988713849741656550813)
    ·
      refine ⟨61115620767693653121206555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162974988713849741656550813 61115620767693653121206555)
      ·
        refine ⟨91673431151540479681809833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61115620767693653121206555 91673431151540479681809833)
        ·
          refine ⟨68755073363655359761357375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91673431151540479681809833 68755073363655359761357375)
          ·
            refine ⟨103132610045483039642036063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68755073363655359761357375 103132610045483039642036063)
            ·
              refine ⟨154698915068224559463054095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103132610045483039642036063 154698915068224559463054095)
              ·
                refine ⟨232048372602336839194581143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154698915068224559463054095 232048372602336839194581143)
                ·
                  refine ⟨348072558903505258791871715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232048372602336839194581143 348072558903505258791871715)
                  ·
                    refine ⟨522108838355257888187807573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 348072558903505258791871715 522108838355257888187807573)
                    ·
                      refine ⟨3059231474737839188600435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 522108838355257888187807573 3059231474737839188600435)
                      ·
                        rfl

theorem cell23_5957832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_5957832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957832 prefixEnd_5957832 := by exact prefixLift 5957832
  have htrace : WordTrace (prefixWord ++ tailWord_5957832) baseStart_5957832 baseEnd_5957832 := by
    simpa [prefixWord, tailWord_5957832, baseEnd_5957832] using wordTrace_append hprefix tailTrace_5957832
  have hstable : (prefixWord ++ tailWord_5957832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957832).length < 2 ^ (prefixWord ++ tailWord_5957832).sum := by decide
  have hdescent : baseEnd_5957832 < baseStart_5957832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957849 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 3]
def baseStart_5957849 : Nat := 118140960795 + 5957849 * 2 ^ 59
def prefixEnd_5957849 : Nat := 4983230072969 + 3 ^ 40 * 5957849 * 2
def baseEnd_5957849 : Nat := 3059240203908965622087857

theorem tailTrace_5957849 : CollatzResearch.WordTrace tailWord_5957849 prefixEnd_5957849 3059240203908965622087857 := by
  unfold tailWord_5957849
  simp only [CollatzResearch.WordTrace]
  refine ⟨217300604992738067445436601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144867069995158711630291067 217300604992738067445436601)
  ·
    refine ⟨162975453744553550584077451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217300604992738067445436601 162975453744553550584077451)
    ·
      refine ⟨244463180616830325876116177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162975453744553550584077451 244463180616830325876116177)
      ·
        refine ⟨183347385462622744407087133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244463180616830325876116177 183347385462622744407087133)
        ·
          refine ⟨68755269548483529152657675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183347385462622744407087133 68755269548483529152657675)
          ·
            refine ⟨103132904322725293728986513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68755269548483529152657675 103132904322725293728986513)
            ·
              refine ⟨77349678242043970296739885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103132904322725293728986513 77349678242043970296739885)
              ·
                refine ⟨29006129340766488861277457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77349678242043970296739885 29006129340766488861277457)
                ·
                  refine ⟨21754597005574866645958093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29006129340766488861277457 21754597005574866645958093)
                  ·
                    refine ⟨8157973877090574992234285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21754597005574866645958093 8157973877090574992234285)
                    ·
                      refine ⟨3059240203908965622087857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8157973877090574992234285 3059240203908965622087857)
                      ·
                        rfl

theorem cell23_5957849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_5957849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957849 prefixEnd_5957849 := by exact prefixLift 5957849
  have htrace : WordTrace (prefixWord ++ tailWord_5957849) baseStart_5957849 baseEnd_5957849 := by
    simpa [prefixWord, tailWord_5957849, baseEnd_5957849] using wordTrace_append hprefix tailTrace_5957849
  have hstable : (prefixWord ++ tailWord_5957849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957849).length < 2 ^ (prefixWord ++ tailWord_5957849).sum := by decide
  have hdescent : baseEnd_5957849 < baseStart_5957849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957850 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2]
def baseStart_5957850 : Nat := 118140960795 + 5957850 * 2 ^ 59
def prefixEnd_5957850 : Nat := 4983230072969 + 3 ^ 40 * 5957850 * 2
def baseEnd_5957850 : Nat := 3059240717389620118175353

theorem tailTrace_5957850 : CollatzResearch.WordTrace tailWord_5957850 prefixEnd_5957850 3059240717389620118175353 := by
  unfold tailWord_5957850
  simp only [CollatzResearch.WordTrace]
  refine ⟨54325160366433611154055751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144867094310489629744148669 54325160366433611154055751)
  ·
    refine ⟨81487740549650416731083627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54325160366433611154055751 81487740549650416731083627)
    ·
      refine ⟨122231610824475625096625441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81487740549650416731083627 122231610824475625096625441)
      ·
        refine ⟨91673708118356718822469081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122231610824475625096625441 91673708118356718822469081)
        ·
          refine ⟨68755281088767539116851811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91673708118356718822469081 68755281088767539116851811)
          ·
            refine ⟨103132921633151308675277717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68755281088767539116851811 103132921633151308675277717)
            ·
              refine ⟨4834355701553967594153643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103132921633151308675277717 4834355701553967594153643)
              ·
                refine ⟨7251533552330951391230465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4834355701553967594153643 7251533552330951391230465)
                ·
                  refine ⟨5438650164248213543422849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7251533552330951391230465 5438650164248213543422849)
                  ·
                    refine ⟨4078987623186160157567137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5438650164248213543422849 4078987623186160157567137)
                    ·
                      refine ⟨3059240717389620118175353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4078987623186160157567137 3059240717389620118175353)
                      ·
                        rfl

theorem cell23_5957850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_5957850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957850 prefixEnd_5957850 := by exact prefixLift 5957850
  have htrace : WordTrace (prefixWord ++ tailWord_5957850) baseStart_5957850 baseEnd_5957850 := by
    simpa [prefixWord, tailWord_5957850, baseEnd_5957850] using wordTrace_append hprefix tailTrace_5957850
  have hstable : (prefixWord ++ tailWord_5957850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957850).length < 2 ^ (prefixWord ++ tailWord_5957850).sum := by decide
  have hdescent : baseEnd_5957850 < baseStart_5957850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957886 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_5957886 : Nat := 118140960795 + 5957886 * 2 ^ 59
def prefixEnd_5957886 : Nat := 4983230072969 + 3 ^ 40 * 5957886 * 2
def baseEnd_5957886 : Nat := 1019753067564393992441729

theorem tailTrace_5957886 : CollatzResearch.WordTrace tailWord_5957886 prefixEnd_5957886 1019753067564393992441729 := by
  unfold tailWord_5957886
  simp only [CollatzResearch.WordTrace]
  refine ⟨27162744311700502845566689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144867969662402681843022341 27162744311700502845566689)
  ·
    refine ⟨20372058233775377134175017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27162744311700502845566689 20372058233775377134175017)
    ·
      refine ⟨15279043675331532850631263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20372058233775377134175017 15279043675331532850631263)
      ·
        refine ⟨22918565512997299275946895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15279043675331532850631263 22918565512997299275946895)
        ·
          refine ⟨34377848269495948913920343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22918565512997299275946895 34377848269495948913920343)
          ·
            refine ⟨51566772404243923370880515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34377848269495948913920343 51566772404243923370880515)
            ·
              refine ⟨77350158606365885056320773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51566772404243923370880515 77350158606365885056320773)
              ·
                refine ⟨14503154738693603448060145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77350158606365885056320773 14503154738693603448060145)
                ·
                  refine ⟨10877366054020202586045109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14503154738693603448060145 10877366054020202586045109)
                  ·
                    refine ⟨1019753067564393992441729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10877366054020202586045109 1019753067564393992441729)
                    ·
                      rfl

theorem cell23_5957886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_5957886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957886 prefixEnd_5957886 := by exact prefixLift 5957886
  have htrace : WordTrace (prefixWord ++ tailWord_5957886) baseStart_5957886 baseEnd_5957886 := by
    simpa [prefixWord, tailWord_5957886, baseEnd_5957886] using wordTrace_append hprefix tailTrace_5957886
  have hstable : (prefixWord ++ tailWord_5957886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957886).length < 2 ^ (prefixWord ++ tailWord_5957886).sum := by decide
  have hdescent : baseEnd_5957886 < baseStart_5957886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957890 : List Nat := [3, 4, 1, 1, 2, 1, 4, 2, 5]
def baseStart_5957890 : Nat := 118140960795 + 5957890 * 2 ^ 59
def prefixEnd_5957890 : Nat := 4983230072969 + 3 ^ 40 * 5957890 * 2
def baseEnd_5957890 : Nat := 339917917401755551297241

theorem tailTrace_5957890 : CollatzResearch.WordTrace tailWord_5957890 prefixEnd_5957890 339917917401755551297241 := by
  unfold tailWord_5957890
  simp only [CollatzResearch.WordTrace]
  refine ⟨54325525096397382861919781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144868066923726354298452749 54325525096397382861919781)
  ·
    refine ⟨10186035955574509286609959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54325525096397382861919781 10186035955574509286609959)
    ·
      refine ⟨15279053933361763929914939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10186035955574509286609959 15279053933361763929914939)
      ·
        refine ⟨22918580900042645894872409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15279053933361763929914939 22918580900042645894872409)
        ·
          refine ⟨17188935675031984421154307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22918580900042645894872409 17188935675031984421154307)
          ·
            refine ⟨25783403512547976631731461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17188935675031984421154307 25783403512547976631731461)
            ·
              refine ⟨4834388158602745618449649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25783403512547976631731461 4834388158602745618449649)
              ·
                refine ⟨3625791118952059213837237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4834388158602745618449649 3625791118952059213837237)
                ·
                  refine ⟨339917917401755551297241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3625791118952059213837237 339917917401755551297241)
                  ·
                    rfl

theorem cell23_5957890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_5957890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957890 prefixEnd_5957890 := by exact prefixLift 5957890
  have htrace : WordTrace (prefixWord ++ tailWord_5957890) baseStart_5957890 baseEnd_5957890 := by
    simpa [prefixWord, tailWord_5957890, baseEnd_5957890] using wordTrace_append hprefix tailTrace_5957890
  have hstable : (prefixWord ++ tailWord_5957890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957890).length < 2 ^ (prefixWord ++ tailWord_5957890).sum := by decide
  have hdescent : baseEnd_5957890 < baseStart_5957890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957946 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 6]
def baseStart_5957946 : Nat := 118140960795 + 5957946 * 2 ^ 59
def prefixEnd_5957946 : Nat := 4983230072969 + 3 ^ 40 * 5957946 * 2
def baseEnd_5957946 : Nat := 339921112392494638063879

theorem tailTrace_5957946 : CollatzResearch.WordTrace tailWord_5957946 prefixEnd_5957946 339921112392494638063879 := by
  unfold tailWord_5957946
  simp only [CollatzResearch.WordTrace]
  refine ⟨54326035718346663252929423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144869428582257768674478461 54326035718346663252929423)
  ·
    refine ⟨81489053577519994879394135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54326035718346663252929423 81489053577519994879394135)
    ·
      refine ⟨122233580366279992319091203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81489053577519994879394135 122233580366279992319091203)
      ·
        refine ⟨183350370549419988478636805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122233580366279992319091203 183350370549419988478636805)
        ·
          refine ⟨34378194478016247839744401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183350370549419988478636805 34378194478016247839744401)
          ·
            refine ⟨25783645858512185879808301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34378194478016247839744401 25783645858512185879808301)
            ·
              refine ⟨9668867196942069704928113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25783645858512185879808301 9668867196942069704928113)
              ·
                refine ⟨7251650397706552278696085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9668867196942069704928113 7251650397706552278696085)
                ·
                  refine ⟨339921112392494638063879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7251650397706552278696085 339921112392494638063879)
                  ·
                    rfl

theorem cell23_5957946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_5957946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957946 prefixEnd_5957946 := by exact prefixLift 5957946
  have htrace : WordTrace (prefixWord ++ tailWord_5957946) baseStart_5957946 baseEnd_5957946 := by
    simpa [prefixWord, tailWord_5957946, baseEnd_5957946] using wordTrace_append hprefix tailTrace_5957946
  have hstable : (prefixWord ++ tailWord_5957946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957946).length < 2 ^ (prefixWord ++ tailWord_5957946).sum := by decide
  have hdescent : baseEnd_5957946 < baseStart_5957946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5957950 : List Nat := [4, 2, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_5957950 : Nat := 118140960795 + 5957950 * 2 ^ 59
def prefixEnd_5957950 : Nat := 4983230072969 + 3 ^ 40 * 5957950 * 2
def baseEnd_5957950 : Nat := 1019764021818356575641631

theorem tailTrace_5957950 : CollatzResearch.WordTrace tailWord_5957950 prefixEnd_5957950 1019764021818356575641631 := by
  unfold tailWord_5957950
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163036095671520211857913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144869525843581441129908869 27163036095671520211857913)
  ·
    refine ⟨20372277071753640158893435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27163036095671520211857913 20372277071753640158893435)
    ·
      refine ⟨30558415607630460238340153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20372277071753640158893435 30558415607630460238340153)
      ·
        refine ⟨22918811705722845178755115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30558415607630460238340153 22918811705722845178755115)
        ·
          refine ⟨34378217558584267768132673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22918811705722845178755115 34378217558584267768132673)
          ·
            refine ⟨25783663168938200826099505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34378217558584267768132673 25783663168938200826099505)
            ·
              refine ⟨19337747376703650619574629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25783663168938200826099505 19337747376703650619574629)
              ·
                refine ⟨3625827633131934491170243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19337747376703650619574629 3625827633131934491170243)
                ·
                  refine ⟨5438741449697901736755365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625827633131934491170243 5438741449697901736755365)
                  ·
                    refine ⟨1019764021818356575641631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5438741449697901736755365 1019764021818356575641631)
                    ·
                      rfl

theorem cell23_5957950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_5957950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5957950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5957950 prefixEnd_5957950 := by exact prefixLift 5957950
  have htrace : WordTrace (prefixWord ++ tailWord_5957950) baseStart_5957950 baseEnd_5957950 := by
    simpa [prefixWord, tailWord_5957950, baseEnd_5957950] using wordTrace_append hprefix tailTrace_5957950
  have hstable : (prefixWord ++ tailWord_5957950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5957950).length < 2 ^ (prefixWord ++ tailWord_5957950).sum := by decide
  have hdescent : baseEnd_5957950 < baseStart_5957950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5957950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958023 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 2, 4]
def baseStart_5958023 : Nat := 118140960795 + 5958023 * 2 ^ 59
def prefixEnd_5958023 : Nat := 4983230072969 + 3 ^ 40 * 5958023 * 2
def baseEnd_5958023 : Nat := 1019776516514282647104019

theorem tailTrace_5958023 : CollatzResearch.WordTrace tailWord_5958023 prefixEnd_5958023 1019776516514282647104019 := by
  unfold tailWord_5958023
  simp only [CollatzResearch.WordTrace]
  refine ⟨217306951294107695162270723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144871300862738463441513815 217306951294107695162270723)
  ·
    refine ⟨325960426941161542743406085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217306951294107695162270723 325960426941161542743406085)
    ·
      refine ⟨61117580051467789264388641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 325960426941161542743406085 61117580051467789264388641)
      ·
        refine ⟨45838185038600841948291481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61117580051467789264388641 45838185038600841948291481)
        ·
          refine ⟨34378638778950631461218611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45838185038600841948291481 34378638778950631461218611)
          ·
            refine ⟨51567958168425947191827917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34378638778950631461218611 51567958168425947191827917)
            ·
              refine ⟨19337984313159730196935469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51567958168425947191827917 19337984313159730196935469)
              ·
                refine ⟨7251744117434898823850801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19337984313159730196935469 7251744117434898823850801)
                ·
                  refine ⟨5438808088076174117888101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7251744117434898823850801 5438808088076174117888101)
                  ·
                    refine ⟨1019776516514282647104019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5438808088076174117888101 1019776516514282647104019)
                    ·
                      rfl

theorem cell23_5958023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_5958023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958023 prefixEnd_5958023 := by exact prefixLift 5958023
  have htrace : WordTrace (prefixWord ++ tailWord_5958023) baseStart_5958023 baseEnd_5958023 := by
    simpa [prefixWord, tailWord_5958023, baseEnd_5958023] using wordTrace_append hprefix tailTrace_5958023
  have hstable : (prefixWord ++ tailWord_5958023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958023).length < 2 ^ (prefixWord ++ tailWord_5958023).sum := by decide
  have hdescent : baseEnd_5958023 < baseStart_5958023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958030 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5958030 : Nat := 118140960795 + 5958030 * 2 ^ 59
def prefixEnd_5958030 : Nat := 4983230072969 + 3 ^ 40 * 5958030 * 2
def baseEnd_5958030 : Nat := 3059333143907429413924525

theorem tailTrace_5958030 : CollatzResearch.WordTrace tailWord_5958030 prefixEnd_5958030 3059333143907429413924525 := by
  unfold tailWord_5958030
  simp only [CollatzResearch.WordTrace]
  refine ⟨27163400825635291919721943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144871471070054890238517029 27163400825635291919721943)
  ·
    refine ⟨40745101238452937879582915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27163400825635291919721943 40745101238452937879582915)
    ·
      refine ⟨61117651857679406819374373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40745101238452937879582915 61117651857679406819374373)
      ·
        refine ⟨11459559723314888778632695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61117651857679406819374373 11459559723314888778632695)
        ·
          refine ⟨17189339584972333167949043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11459559723314888778632695 17189339584972333167949043)
          ·
            refine ⟨25784009377458499751923565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17189339584972333167949043 25784009377458499751923565)
            ·
              refine ⟨9669003516546937406971337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25784009377458499751923565 9669003516546937406971337)
              ·
                refine ⟨7251752637410203055228503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9669003516546937406971337 7251752637410203055228503)
                ·
                  refine ⟨10877628956115304582842755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7251752637410203055228503 10877628956115304582842755)
                  ·
                    refine ⟨16316443434172956874264133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10877628956115304582842755 16316443434172956874264133)
                    ·
                      refine ⟨3059333143907429413924525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16316443434172956874264133 3059333143907429413924525)
                      ·
                        rfl

theorem cell23_5958030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5958030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958030 prefixEnd_5958030 := by exact prefixLift 5958030
  have htrace : WordTrace (prefixWord ++ tailWord_5958030) baseStart_5958030 baseEnd_5958030 := by
    simpa [prefixWord, tailWord_5958030, baseEnd_5958030] using wordTrace_append hprefix tailTrace_5958030
  have hstable : (prefixWord ++ tailWord_5958030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958030).length < 2 ^ (prefixWord ++ tailWord_5958030).sum := by decide
  have hdescent : baseEnd_5958030 < baseStart_5958030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958047 : List Nat := [1, 1, 2, 5, 1, 1, 2, 5, 1, 2, 2]
def baseStart_5958047 : Nat := 118140960795 + 5958047 * 2 ^ 59
def prefixEnd_5958047 : Nat := 4983230072969 + 3 ^ 40 * 5958047 * 2
def baseEnd_5958047 : Nat := 3059341873078555847411947

theorem tailTrace_5958047 : CollatzResearch.WordTrace tailWord_5958047 prefixEnd_5958047 3059341873078555847411947 := by
  unfold tailWord_5958047
  simp only [CollatzResearch.WordTrace]
  refine ⟨217307826646020747261144395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144871884430680498174096263 217307826646020747261144395)
  ·
    refine ⟨325961739969031120891716593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217307826646020747261144395 325961739969031120891716593)
    ·
      refine ⟨244471304976773340668787445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325961739969031120891716593 244471304976773340668787445)
      ·
        refine ⟨22919184841572500687698823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244471304976773340668787445 22919184841572500687698823)
        ·
          refine ⟨34378777262358751031548235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22919184841572500687698823 34378777262358751031548235)
          ·
            refine ⟨51568165893538126547322353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34378777262358751031548235 51568165893538126547322353)
            ·
              refine ⟨38676124420153594910491765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51568165893538126547322353 38676124420153594910491765)
              ·
                refine ⟨3625886664389399522858603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38676124420153594910491765 3625886664389399522858603)
                ·
                  refine ⟨5438829996584099284287905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625886664389399522858603 5438829996584099284287905)
                  ·
                    refine ⟨4079122497438074463215929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5438829996584099284287905 4079122497438074463215929)
                    ·
                      refine ⟨3059341873078555847411947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079122497438074463215929 3059341873078555847411947)
                      ·
                        rfl

theorem cell23_5958047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_5958047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958047 prefixEnd_5958047 := by exact prefixLift 5958047
  have htrace : WordTrace (prefixWord ++ tailWord_5958047) baseStart_5958047 baseEnd_5958047 := by
    simpa [prefixWord, tailWord_5958047, baseEnd_5958047] using wordTrace_append hprefix tailTrace_5958047
  have hstable : (prefixWord ++ tailWord_5958047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958047).length < 2 ^ (prefixWord ++ tailWord_5958047).sum := by decide
  have hdescent : baseEnd_5958047 < baseStart_5958047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958081 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5958081 : Nat := 118140960795 + 5958081 * 2 ^ 59
def prefixEnd_5958081 : Nat := 4983230072969 + 3 ^ 40 * 5958081 * 2
def baseEnd_5958081 : Nat := 3059359331420808714386791

theorem tailTrace_5958081 : CollatzResearch.WordTrace tailWord_5958081 prefixEnd_5958081 3059359331420808714386791 := by
  unfold tailWord_5958081
  simp only [CollatzResearch.WordTrace]
  refine ⟨217309066727897571067882097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144872711151931714045254731 217309066727897571067882097)
  ·
    refine ⟨162981800045923178300911573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217309066727897571067882097 162981800045923178300911573)
    ·
      refine ⟨3819885938576324491427615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 162981800045923178300911573 3819885938576324491427615)
      ·
        refine ⟨5729828907864486737141423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819885938576324491427615 5729828907864486737141423)
        ·
          refine ⟨8594743361796730105712135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729828907864486737141423 8594743361796730105712135)
          ·
            refine ⟨12892115042695095158568203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594743361796730105712135 12892115042695095158568203)
            ·
              refine ⟨19338172564042642737852305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892115042695095158568203 19338172564042642737852305)
              ·
                refine ⟨14503629423031982053389229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19338172564042642737852305 14503629423031982053389229)
                ·
                  refine ⟨5438861033636993270020961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14503629423031982053389229 5438861033636993270020961)
                  ·
                    refine ⟨4079145775227744952515721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5438861033636993270020961 4079145775227744952515721)
                    ·
                      refine ⟨3059359331420808714386791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079145775227744952515721 3059359331420808714386791)
                      ·
                        rfl

theorem cell23_5958081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5958081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958081 prefixEnd_5958081 := by exact prefixLift 5958081
  have htrace : WordTrace (prefixWord ++ tailWord_5958081) baseStart_5958081 baseEnd_5958081 := by
    simpa [prefixWord, tailWord_5958081, baseEnd_5958081] using wordTrace_append hprefix tailTrace_5958081
  have hstable : (prefixWord ++ tailWord_5958081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958081).length < 2 ^ (prefixWord ++ tailWord_5958081).sum := by decide
  have hdescent : baseEnd_5958081 < baseStart_5958081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958090 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_5958090 : Nat := 118140960795 + 5958090 * 2 ^ 59
def prefixEnd_5958090 : Nat := 4983230072969 + 3 ^ 40 * 5958090 * 2
def baseEnd_5958090 : Nat := 3059363952746699179174249

theorem tailTrace_5958090 : CollatzResearch.WordTrace tailWord_5958090 prefixEnd_5958090 3059363952746699179174249 := by
  unfold tailWord_5958090
  simp only [CollatzResearch.WordTrace]
  refine ⟨54327348746216241401239931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144872929989909977069973149 54327348746216241401239931)
  ·
    refine ⟨81491023119324362101859897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54327348746216241401239931 81491023119324362101859897)
    ·
      refine ⟨61118267339493271576394923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81491023119324362101859897 61118267339493271576394923)
      ·
        refine ⟨91677401009239907364592385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61118267339493271576394923 91677401009239907364592385)
        ·
          refine ⟨68758050756929930523444289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91677401009239907364592385 68758050756929930523444289)
          ·
            refine ⟨51568538067697447892583217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68758050756929930523444289 51568538067697447892583217)
            ·
              refine ⟨38676403550773085919437413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51568538067697447892583217 38676403550773085919437413)
              ·
                refine ⟨7251825665769953609894515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38676403550773085919437413 7251825665769953609894515)
                ·
                  refine ⟨10877738498654930414841773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7251825665769953609894515 10877738498654930414841773)
                  ·
                    refine ⟨4079151936995598905565665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10877738498654930414841773 4079151936995598905565665)
                    ·
                      refine ⟨3059363952746699179174249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079151936995598905565665 3059363952746699179174249)
                      ·
                        rfl

theorem cell23_5958090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_5958090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958090 prefixEnd_5958090 := by exact prefixLift 5958090
  have htrace : WordTrace (prefixWord ++ tailWord_5958090) baseStart_5958090 baseEnd_5958090 := by
    simpa [prefixWord, tailWord_5958090, baseEnd_5958090] using wordTrace_append hprefix tailTrace_5958090
  have hstable : (prefixWord ++ tailWord_5958090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958090).length < 2 ^ (prefixWord ++ tailWord_5958090).sum := by decide
  have hdescent : baseEnd_5958090 < baseStart_5958090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958106 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_5958106 : Nat := 118140960795 + 5958106 * 2 ^ 59
def prefixEnd_5958106 : Nat := 4983230072969 + 3 ^ 40 * 5958106 * 2
def baseEnd_5958106 : Nat := 3059372168437171116574175

theorem tailTrace_5958106 : CollatzResearch.WordTrace tailWord_5958106 prefixEnd_5958106 3059372168437171116574175 := by
  unfold tailWord_5958106
  simp only [CollatzResearch.WordTrace]
  refine ⟨54327494638201750084385543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144873319035204666891694781 54327494638201750084385543)
  ·
    refine ⟨81491241957302625126578315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54327494638201750084385543 81491241957302625126578315)
    ·
      refine ⟨122236862935953937689867473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81491241957302625126578315 122236862935953937689867473)
      ·
        refine ⟨91677647201965453267400605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122236862935953937689867473 91677647201965453267400605)
        ·
          refine ⟨34379117700737044975275227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91677647201965453267400605 34379117700737044975275227)
          ·
            refine ⟨51568676551105567462912841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34379117700737044975275227 51568676551105567462912841)
            ·
              refine ⟨38676507413329175597184631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51568676551105567462912841 38676507413329175597184631)
              ·
                refine ⟨58014761119993763395776947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38676507413329175597184631 58014761119993763395776947)
                ·
                  refine ⟨87022141679990645093665421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58014761119993763395776947 87022141679990645093665421)
                  ·
                    refine ⟨32633303129996491910124533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87022141679990645093665421 32633303129996491910124533)
                    ·
                      refine ⟨3059372168437171116574175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32633303129996491910124533 3059372168437171116574175)
                      ·
                        rfl

theorem cell23_5958106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_5958106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958106 prefixEnd_5958106 := by exact prefixLift 5958106
  have htrace : WordTrace (prefixWord ++ tailWord_5958106) baseStart_5958106 baseEnd_5958106 := by
    simpa [prefixWord, tailWord_5958106, baseEnd_5958106] using wordTrace_append hprefix tailTrace_5958106
  have hstable : (prefixWord ++ tailWord_5958106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958106).length < 2 ^ (prefixWord ++ tailWord_5958106).sum := by decide
  have hdescent : baseEnd_5958106 < baseStart_5958106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958114 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5958114 : Nat := 118140960795 + 5958114 * 2 ^ 59
def prefixEnd_5958114 : Nat := 4983230072969 + 3 ^ 40 * 5958114 * 2
def baseEnd_5958114 : Nat := 3059376276282407085274139

theorem tailTrace_5958114 : CollatzResearch.WordTrace tailWord_5958114 prefixEnd_5958114 3059376276282407085274139 := by
  unfold tailWord_5958114
  simp only [CollatzResearch.WordTrace]
  refine ⟨54327567584194504425958349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144873513557852011802555597 54327567584194504425958349)
  ·
    refine ⟨20372837844072939159734381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54327567584194504425958349 20372837844072939159734381)
    ·
      refine ⟨7639814191527352184900393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20372837844072939159734381 7639814191527352184900393)
      ·
        refine ⟨5729860643645514138675295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7639814191527352184900393 5729860643645514138675295)
        ·
          refine ⟨8594790965468271208012943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729860643645514138675295 8594790965468271208012943)
          ·
            refine ⟨12892186448202406812019415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8594790965468271208012943 12892186448202406812019415)
            ·
              refine ⟨19338279672303610218029123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892186448202406812019415 19338279672303610218029123)
              ·
                refine ⟨29007419508455415327043685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19338279672303610218029123 29007419508455415327043685)
                ·
                  refine ⟨5438891157835390373820691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29007419508455415327043685 5438891157835390373820691)
                  ·
                    refine ⟨8158336736753085560731037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5438891157835390373820691 8158336736753085560731037)
                    ·
                      refine ⟨3059376276282407085274139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8158336736753085560731037 3059376276282407085274139)
                      ·
                        rfl

theorem cell23_5958114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5958114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958114 prefixEnd_5958114 := by exact prefixLift 5958114
  have htrace : WordTrace (prefixWord ++ tailWord_5958114) baseStart_5958114 baseEnd_5958114 := by
    simpa [prefixWord, tailWord_5958114, baseEnd_5958114] using wordTrace_append hprefix tailTrace_5958114
  have hstable : (prefixWord ++ tailWord_5958114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958114).length < 2 ^ (prefixWord ++ tailWord_5958114).sum := by decide
  have hdescent : baseEnd_5958114 < baseStart_5958114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958157 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5958157 : Nat := 118140960795 + 5958157 * 2 ^ 59
def prefixEnd_5958157 : Nat := 4983230072969 + 3 ^ 40 * 5958157 * 2
def baseEnd_5958157 : Nat := 3059398355950550417036441

theorem tailTrace_5958157 : CollatzResearch.WordTrace tailWord_5958157 prefixEnd_5958157 3059398355950550417036441 := by
  unfold tailWord_5958157
  simp only [CollatzResearch.WordTrace]
  refine ⟨217311838675622236047648725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144874559117081490698432483 217311838675622236047648725)
  ·
    refine ⟨5093246218959896157366767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 217311838675622236047648725 5093246218959896157366767)
    ·
      refine ⟨7639869328439844236050151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5093246218959896157366767 7639869328439844236050151)
      ·
        refine ⟨11459803992659766354075227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7639869328439844236050151 11459803992659766354075227)
        ·
          refine ⟨17189705988989649531112841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11459803992659766354075227 17189705988989649531112841)
          ·
            refine ⟨12892279491742237148334631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17189705988989649531112841 12892279491742237148334631)
            ·
              refine ⟨19338419237613355722501947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892279491742237148334631 19338419237613355722501947)
              ·
                refine ⟨29007628856420033583752921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19338419237613355722501947 29007628856420033583752921)
                ·
                  refine ⟨21755721642315025187814691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29007628856420033583752921 21755721642315025187814691)
                  ·
                    refine ⟨32633582463472537781722037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21755721642315025187814691 32633582463472537781722037)
                    ·
                      refine ⟨3059398355950550417036441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32633582463472537781722037 3059398355950550417036441)
                      ·
                        rfl

theorem cell23_5958157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5958157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958157 prefixEnd_5958157 := by exact prefixLift 5958157
  have htrace : WordTrace (prefixWord ++ tailWord_5958157) baseStart_5958157 baseEnd_5958157 := by
    simpa [prefixWord, tailWord_5958157, baseEnd_5958157] using wordTrace_append hprefix tailTrace_5958157
  have hstable : (prefixWord ++ tailWord_5958157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958157).length < 2 ^ (prefixWord ++ tailWord_5958157).sum := by decide
  have hdescent : baseEnd_5958157 < baseStart_5958157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958173 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_5958173 : Nat := 118140960795 + 5958173 * 2 ^ 59
def prefixEnd_5958173 : Nat := 4983230072969 + 3 ^ 40 * 5958173 * 2
def baseEnd_5958173 : Nat := 1019802190547007451478789

theorem tailTrace_5958173 : CollatzResearch.WordTrace tailWord_5958173 prefixEnd_5958173 1019802190547007451478789 := by
  unfold tailWord_5958173
  simp only [CollatzResearch.WordTrace]
  refine ⟨217312422243564270780231173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144874948162376180520154115 217312422243564270780231173)
  ·
    refine ⟨40746079170668300771293345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217312422243564270780231173 40746079170668300771293345)
    ·
      refine ⟨30559559378001225578470009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40746079170668300771293345 30559559378001225578470009)
      ·
        refine ⟨22919669533500919183852507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30559559378001225578470009 22919669533500919183852507)
        ·
          refine ⟨34379504300251378775778761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22919669533500919183852507 34379504300251378775778761)
          ·
            refine ⟨25784628225188534081834071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34379504300251378775778761 25784628225188534081834071)
            ·
              refine ⟨38676942337782801122751107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25784628225188534081834071 38676942337782801122751107)
              ·
                refine ⟨58015413506674201684126661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38676942337782801122751107 58015413506674201684126661)
                ·
                  refine ⟨10877890032501412815773749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58015413506674201684126661 10877890032501412815773749)
                  ·
                    refine ⟨1019802190547007451478789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10877890032501412815773749 1019802190547007451478789)
                    ·
                      rfl

theorem cell23_5958173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_5958173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958173 prefixEnd_5958173 := by exact prefixLift 5958173
  have htrace : WordTrace (prefixWord ++ tailWord_5958173) baseStart_5958173 baseEnd_5958173 := by
    simpa [prefixWord, tailWord_5958173, baseEnd_5958173] using wordTrace_append hprefix tailTrace_5958173
  have hstable : (prefixWord ++ tailWord_5958173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958173).length < 2 ^ (prefixWord ++ tailWord_5958173).sum := by decide
  have hdescent : baseEnd_5958173 < baseStart_5958173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958216 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 10]
def baseStart_5958216 : Nat := 118140960795 + 5958216 * 2 ^ 59
def prefixEnd_5958216 : Nat := 4983230072969 + 3 ^ 40 * 5958216 * 2
def baseEnd_5958216 : Nat := 339936516812129520688741

theorem tailTrace_5958216 : CollatzResearch.WordTrace tailWord_5958216 prefixEnd_5958216 339936516812129520688741 := by
  unfold tailWord_5958216
  simp only [CollatzResearch.WordTrace]
  refine ⟨108656995291204244562023251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144875993721605659416031001 108656995291204244562023251)
  ·
    refine ⟨162985492936806366843034877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108656995291204244562023251 162985492936806366843034877)
    ·
      refine ⟨61119559851302387566138079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162985492936806366843034877 61119559851302387566138079)
      ·
        refine ⟨91679339776953581349207119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61119559851302387566138079 91679339776953581349207119)
        ·
          refine ⟨137519009665430372023810679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91679339776953581349207119 137519009665430372023810679)
          ·
            refine ⟨206278514498145558035716019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137519009665430372023810679 206278514498145558035716019)
            ·
              refine ⟨309417771747218337053574029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206278514498145558035716019 309417771747218337053574029)
              ·
                refine ⟨116031664405206876395090261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309417771747218337053574029 116031664405206876395090261)
                ·
                  refine ⟨339936516812129520688741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 116031664405206876395090261 339936516812129520688741)
                  ·
                    rfl

theorem cell23_5958216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 10].length) (baseStart_5958216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958216 prefixEnd_5958216 := by exact prefixLift 5958216
  have htrace : WordTrace (prefixWord ++ tailWord_5958216) baseStart_5958216 baseEnd_5958216 := by
    simpa [prefixWord, tailWord_5958216, baseEnd_5958216] using wordTrace_append hprefix tailTrace_5958216
  have hstable : (prefixWord ++ tailWord_5958216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958216).length < 2 ^ (prefixWord ++ tailWord_5958216).sum := by decide
  have hdescent : baseEnd_5958216 < baseStart_5958216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958263 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 3, 5]
def baseStart_5958263 : Nat := 118140960795 + 5958263 * 2 ^ 59
def prefixEnd_5958263 : Nat := 4983230072969 + 3 ^ 40 * 5958263 * 2
def baseEnd_5958263 : Nat := 1019817594966642334103651

theorem tailTrace_5958263 : CollatzResearch.WordTrace tailWord_5958263 prefixEnd_5958263 1019817594966642334103651 := by
  unfold tailWord_5958263
  simp only [CollatzResearch.WordTrace]
  refine ⟨217315704813238216151007443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144877136542158810767338295 217315704813238216151007443)
  ·
    refine ⟨325973557219857324226511165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217315704813238216151007443 325973557219857324226511165)
    ·
      refine ⟨122240083957446496584941687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325973557219857324226511165 122240083957446496584941687)
      ·
        refine ⟨183360125936169744877412531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122240083957446496584941687 183360125936169744877412531)
        ·
          refine ⟨275040188904254617316118797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183360125936169744877412531 275040188904254617316118797)
          ·
            refine ⟨103140070839095481493544549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275040188904254617316118797 103140070839095481493544549)
            ·
              refine ⟨19338763282330402780039603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103140070839095481493544549 19338763282330402780039603)
              ·
                refine ⟨29008144923495604170059405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19338763282330402780039603 29008144923495604170059405)
                ·
                  refine ⟨10878054346310851563772277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29008144923495604170059405 10878054346310851563772277)
                  ·
                    refine ⟨1019817594966642334103651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10878054346310851563772277 1019817594966642334103651)
                    ·
                      rfl

theorem cell23_5958263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_5958263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958263 prefixEnd_5958263 := by exact prefixLift 5958263
  have htrace : WordTrace (prefixWord ++ tailWord_5958263) baseStart_5958263 baseEnd_5958263 := by
    simpa [prefixWord, tailWord_5958263, baseEnd_5958263] using wordTrace_append hprefix tailTrace_5958263
  have hstable : (prefixWord ++ tailWord_5958263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958263).length < 2 ^ (prefixWord ++ tailWord_5958263).sum := by decide
  have hdescent : baseEnd_5958263 < baseStart_5958263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958283 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 4]
def baseStart_5958283 : Nat := 118140960795 + 5958283 * 2 ^ 59
def prefixEnd_5958283 : Nat := 4983230072969 + 3 ^ 40 * 5958283 * 2
def baseEnd_5958283 : Nat := 3059463054513016924060861

theorem tailTrace_5958283 : CollatzResearch.WordTrace tailWord_5958283 prefixEnd_5958283 3059463054513016924060861 := by
  unfold tailWord_5958283
  simp only [CollatzResearch.WordTrace]
  refine ⟨217316434273165759566735503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144877622848777173044490335 217316434273165759566735503)
  ·
    refine ⟨325974651409748639350103255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217316434273165759566735503 325974651409748639350103255)
    ·
      refine ⟨488961977114622959025154883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325974651409748639350103255 488961977114622959025154883)
      ·
        refine ⟨733442965671934438537732325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488961977114622959025154883 733442965671934438537732325)
        ·
          refine ⟨137520556063487707225824811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 733442965671934438537732325 137520556063487707225824811)
          ·
            refine ⟨206280834095231560838737217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137520556063487707225824811 206280834095231560838737217)
            ·
              refine ⟨154710625571423670629052913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206280834095231560838737217 154710625571423670629052913)
              ·
                refine ⟨116032969178567752971789685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154710625571423670629052913 116032969178567752971789685)
                ·
                  refine ⟨10878090860490726841105283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116032969178567752971789685 10878090860490726841105283)
                  ·
                    refine ⟨16317136290736090261657925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10878090860490726841105283 16317136290736090261657925)
                    ·
                      refine ⟨3059463054513016924060861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16317136290736090261657925 3059463054513016924060861)
                      ·
                        rfl

theorem cell23_5958283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 4].length) (baseStart_5958283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958283 prefixEnd_5958283 := by exact prefixLift 5958283
  have htrace : WordTrace (prefixWord ++ tailWord_5958283) baseStart_5958283 baseEnd_5958283 := by
    simpa [prefixWord, tailWord_5958283, baseEnd_5958283] using wordTrace_append hprefix tailTrace_5958283
  have hstable : (prefixWord ++ tailWord_5958283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958283).length < 2 ^ (prefixWord ++ tailWord_5958283).sum := by decide
  have hdescent : baseEnd_5958283 < baseStart_5958283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958317 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_5958317 : Nat := 118140960795 + 5958317 * 2 ^ 59
def prefixEnd_5958317 : Nat := 4983230072969 + 3 ^ 40 * 5958317 * 2
def baseEnd_5958317 : Nat := 3059480512855269791035705

theorem tailTrace_5958317 : CollatzResearch.WordTrace tailWord_5958317 prefixEnd_5958317 3059480512855269791035705 := by
  unfold tailWord_5958317
  simp only [CollatzResearch.WordTrace]
  refine ⟨217317674355042583373473205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144878449570028388915648803 217317674355042583373473205)
  ·
    refine ⟨20373531970785242191263113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217317674355042583373473205 20373531970785242191263113)
    ·
      refine ⟨15280148978088931643447335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20373531970785242191263113 15280148978088931643447335)
      ·
        refine ⟨22920223467133397465171003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15280148978088931643447335 22920223467133397465171003)
        ·
          refine ⟨34380335200700096197756505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22920223467133397465171003 34380335200700096197756505)
          ·
            refine ⟨25785251400525072148317379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34380335200700096197756505 25785251400525072148317379)
            ·
              refine ⟨38677877100787608222476069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25785251400525072148317379 38677877100787608222476069)
              ·
                refine ⟨7252101956397676541714263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38677877100787608222476069 7252101956397676541714263)
                ·
                  refine ⟨10878152934596514812571395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7252101956397676541714263 10878152934596514812571395)
                  ·
                    refine ⟨16317229401894772218857093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10878152934596514812571395 16317229401894772218857093)
                    ·
                      refine ⟨3059480512855269791035705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16317229401894772218857093 3059480512855269791035705)
                      ·
                        rfl

theorem cell23_5958317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_5958317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958317 prefixEnd_5958317 := by exact prefixLift 5958317
  have htrace : WordTrace (prefixWord ++ tailWord_5958317) baseStart_5958317 baseEnd_5958317 := by
    simpa [prefixWord, tailWord_5958317, baseEnd_5958317] using wordTrace_append hprefix tailTrace_5958317
  have hstable : (prefixWord ++ tailWord_5958317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958317).length < 2 ^ (prefixWord ++ tailWord_5958317).sum := by decide
  have hdescent : baseEnd_5958317 < baseStart_5958317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958323 : List Nat := [1, 1, 1, 2, 3, 5, 1, 9]
def baseStart_5958323 : Nat := 118140960795 + 5958323 * 2 ^ 59
def prefixEnd_5958323 : Nat := 4983230072969 + 3 ^ 40 * 5958323 * 2
def baseEnd_5958323 : Nat := 113314207175525806205951

theorem tailTrace_5958323 : CollatzResearch.WordTrace tailWord_5958323 prefixEnd_5958323 113314207175525806205951 := by
  unfold tailWord_5958323
  simp only [CollatzResearch.WordTrace]
  refine ⟨217317893193020846398191623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144878595462013897598794415 217317893193020846398191623)
  ·
    refine ⟨325976839789531269597287435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217317893193020846398191623 325976839789531269597287435)
    ·
      refine ⟨488965259684296904395931153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325976839789531269597287435 488965259684296904395931153)
      ·
        refine ⟨366723944763222678296948365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488965259684296904395931153 366723944763222678296948365)
        ·
          refine ⟨137521479286208504361355637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366723944763222678296948365 137521479286208504361355637)
          ·
            refine ⟨12892638683082047283877091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137521479286208504361355637 12892638683082047283877091)
            ·
              refine ⟨19338958024623070925815637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12892638683082047283877091 19338958024623070925815637)
              ·
                refine ⟨113314207175525806205951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19338958024623070925815637 113314207175525806205951)
                ·
                  rfl

theorem cell23_5958323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 9].length) (baseStart_5958323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958323 prefixEnd_5958323 := by exact prefixLift 5958323
  have htrace : WordTrace (prefixWord ++ tailWord_5958323) baseStart_5958323 baseEnd_5958323 := by
    simpa [prefixWord, tailWord_5958323, baseEnd_5958323] using wordTrace_append hprefix tailTrace_5958323
  have hstable : (prefixWord ++ tailWord_5958323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958323).length < 2 ^ (prefixWord ++ tailWord_5958323).sum := by decide
  have hdescent : baseEnd_5958323 < baseStart_5958323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958340 : List Nat := [2, 3, 3, 1, 1, 4, 9]
def baseStart_5958340 : Nat := 118140960795 + 5958340 * 2 ^ 59
def prefixEnd_5958340 : Nat := 4983230072969 + 3 ^ 40 * 5958340 * 2
def baseEnd_5958340 : Nat := 37771510159386706185779

theorem tailTrace_5958340 : CollatzResearch.WordTrace tailWord_5958340 prefixEnd_5958340 37771510159386706185779 := by
  unfold tailWord_5958340
  simp only [CollatzResearch.WordTrace]
  refine ⟨108659256616979629150780237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144879008822639505534373649 108659256616979629150780237)
  ·
    refine ⟨40747221231367360931542589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108659256616979629150780237 40747221231367360931542589)
    ·
      refine ⟨15280207961762760349328471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40747221231367360931542589 15280207961762760349328471)
      ·
        refine ⟨22920311942644140523992707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15280207961762760349328471 22920311942644140523992707)
        ·
          refine ⟨34380467913966210785989061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22920311942644140523992707 34380467913966210785989061)
          ·
            refine ⟨6446337733868664522372949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34380467913966210785989061 6446337733868664522372949)
            ·
              refine ⟨37771510159386706185779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6446337733868664522372949 37771510159386706185779)
              ·
                rfl

theorem cell23_5958340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 9].length) (baseStart_5958340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958340 prefixEnd_5958340 := by exact prefixLift 5958340
  have htrace : WordTrace (prefixWord ++ tailWord_5958340) baseStart_5958340 baseEnd_5958340 := by
    simpa [prefixWord, tailWord_5958340, baseEnd_5958340] using wordTrace_append hprefix tailTrace_5958340
  have hstable : (prefixWord ++ tailWord_5958340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958340).length < 2 ^ (prefixWord ++ tailWord_5958340).sum := by decide
  have hdescent : baseEnd_5958340 < baseStart_5958340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958353 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 2, 7]
def baseStart_5958353 : Nat := 118140960795 + 5958353 * 2 ^ 59
def prefixEnd_5958353 : Nat := 4983230072969 + 3 ^ 40 * 5958353 * 2
def baseEnd_5958353 : Nat := 1019832999386277216728513

theorem tailTrace_5958353 : CollatzResearch.WordTrace tailWord_5958353 prefixEnd_5958353 1019832999386277216728513 := by
  unfold tailWord_5958353
  simp only [CollatzResearch.WordTrace]
  refine ⟨217318987382912161521783713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144879324921941441014522475 217318987382912161521783713)
  ·
    refine ⟨162989240537184121141337785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217318987382912161521783713 162989240537184121141337785)
    ·
      refine ⟨122241930402888090856003339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162989240537184121141337785 122241930402888090856003339)
      ·
        refine ⟨183362895604332136284005009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122241930402888090856003339 183362895604332136284005009)
        ·
          refine ⟨137522171703249102213003757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183362895604332136284005009 137522171703249102213003757)
          ·
            refine ⟨51570814388718413329876409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137522171703249102213003757 51570814388718413329876409)
            ·
              refine ⟨38678110791538809997407307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51570814388718413329876409 38678110791538809997407307)
              ·
                refine ⟨58017166187308214996110961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38678110791538809997407307 58017166187308214996110961)
                ·
                  refine ⟨43512874640481161247083221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58017166187308214996110961 43512874640481161247083221)
                  ·
                    refine ⟨1019832999386277216728513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43512874640481161247083221 1019832999386277216728513)
                    ·
                      rfl

theorem cell23_5958353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_5958353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958353 prefixEnd_5958353 := by exact prefixLift 5958353
  have htrace : WordTrace (prefixWord ++ tailWord_5958353) baseStart_5958353 baseEnd_5958353 := by
    simpa [prefixWord, tailWord_5958353, baseEnd_5958353] using wordTrace_append hprefix tailTrace_5958353
  have hstable : (prefixWord ++ tailWord_5958353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958353).length < 2 ^ (prefixWord ++ tailWord_5958353).sum := by decide
  have hdescent : baseEnd_5958353 < baseStart_5958353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958357 : List Nat := [1, 3, 2, 5, 1, 1, 2, 8]
def baseStart_5958357 : Nat := 118140960795 + 5958357 * 2 ^ 59
def prefixEnd_5958357 : Nat := 4983230072969 + 3 ^ 40 * 5958357 * 2
def baseEnd_5958357 : Nat := 113314853780794430908723

theorem tailTrace_5958357 : CollatzResearch.WordTrace tailWord_5958357 prefixEnd_5958357 113314853780794430908723 := by
  unfold tailWord_5958357
  simp only [CollatzResearch.WordTrace]
  refine ⟨217319133274897670204929325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144879422183265113469952883 217319133274897670204929325)
  ·
    refine ⟨81494674978086626326848497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217319133274897670204929325 81494674978086626326848497)
    ·
      refine ⟨61121006233564969745136373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81494674978086626326848497 61121006233564969745136373)
      ·
        refine ⟨5730094334396715913606535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61121006233564969745136373 5730094334396715913606535)
        ·
          refine ⟨8595141501595073870409803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5730094334396715913606535 8595141501595073870409803)
          ·
            refine ⟨12892712252392610805614705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8595141501595073870409803 12892712252392610805614705)
            ·
              refine ⟨9669534189294458104211029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12892712252392610805614705 9669534189294458104211029)
              ·
                refine ⟨113314853780794430908723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9669534189294458104211029 113314853780794430908723)
                ·
                  rfl

theorem cell23_5958357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 8].length) (baseStart_5958357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958357 prefixEnd_5958357 := by exact prefixLift 5958357
  have htrace : WordTrace (prefixWord ++ tailWord_5958357) baseStart_5958357 baseEnd_5958357 := by
    simpa [prefixWord, tailWord_5958357, baseEnd_5958357] using wordTrace_append hprefix tailTrace_5958357
  have hstable : (prefixWord ++ tailWord_5958357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958357).length < 2 ^ (prefixWord ++ tailWord_5958357).sum := by decide
  have hdescent : baseEnd_5958357 < baseStart_5958357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958388 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5958388 : Nat := 118140960795 + 5958388 * 2 ^ 59
def prefixEnd_5958388 : Nat := 4983230072969 + 3 ^ 40 * 5958388 * 2
def baseEnd_5958388 : Nat := 3059516969981739013247879

theorem tailTrace_5958388 : CollatzResearch.WordTrace tailWord_5958388 prefixEnd_5958388 3059516969981739013247879 := by
  unfold tailWord_5958388
  simp only [CollatzResearch.WordTrace]
  refine ⟨108660131968892681249653909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144880175958523574999538545 108660131968892681249653909)
  ·
    refine ⟨5093443686041844433577527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108660131968892681249653909 5093443686041844433577527)
    ·
      refine ⟨7640165529062766650366291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5093443686041844433577527 7640165529062766650366291)
      ·
        refine ⟨11460248293594149975549437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7640165529062766650366291 11460248293594149975549437)
        ·
          refine ⟨4297593110097806240831039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11460248293594149975549437 4297593110097806240831039)
          ·
            refine ⟨6446389665146709361246559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297593110097806240831039 6446389665146709361246559)
            ·
              refine ⟨9669584497720064041869839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6446389665146709361246559 9669584497720064041869839)
              ·
                refine ⟨14504376746580096062804759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9669584497720064041869839 14504376746580096062804759)
                ·
                  refine ⟨21756565119870144094207139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14504376746580096062804759 21756565119870144094207139)
                  ·
                    refine ⟨32634847679805216141310709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21756565119870144094207139 32634847679805216141310709)
                    ·
                      refine ⟨3059516969981739013247879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32634847679805216141310709 3059516969981739013247879)
                      ·
                        rfl

theorem cell23_5958388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5958388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958388 prefixEnd_5958388 := by exact prefixLift 5958388
  have htrace : WordTrace (prefixWord ++ tailWord_5958388) baseStart_5958388 baseEnd_5958388 := by
    simpa [prefixWord, tailWord_5958388, baseEnd_5958388] using wordTrace_append hprefix tailTrace_5958388
  have hstable : (prefixWord ++ tailWord_5958388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958388).length < 2 ^ (prefixWord ++ tailWord_5958388).sum := by decide
  have hdescent : baseEnd_5958388 < baseStart_5958388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958403 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6]
def baseStart_5958403 : Nat := 118140960795 + 5958403 * 2 ^ 59
def prefixEnd_5958403 : Nat := 4983230072969 + 3 ^ 40 * 5958403 * 2
def baseEnd_5958403 : Nat := 3059524672191556454560309

theorem tailTrace_5958403 : CollatzResearch.WordTrace tailWord_5958403 prefixEnd_5958403 3059524672191556454560309 := by
  unfold tailWord_5958403
  simp only [CollatzResearch.WordTrace]
  refine ⟨217320811032731020061103863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144880540688487346707402575 217320811032731020061103863)
  ·
    refine ⟨325981216549096530091655795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217320811032731020061103863 325981216549096530091655795)
    ·
      refine ⟨488971824823644795137483693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325981216549096530091655795 488971824823644795137483693)
      ·
        refine ⟨183364434308866798176556385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 488971824823644795137483693 183364434308866798176556385)
        ·
          refine ⟨137523325731650098632417289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183364434308866798176556385 137523325731650098632417289)
          ·
            refine ⟨103142494298737573974312967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137523325731650098632417289 103142494298737573974312967)
            ·
              refine ⟨154713741448106360961469451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103142494298737573974312967 154713741448106360961469451)
              ·
                refine ⟨232070612172159541442204177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154713741448106360961469451 232070612172159541442204177)
                ·
                  refine ⟨174052959129119656081653133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232070612172159541442204177 174052959129119656081653133)
                  ·
                    refine ⟨65269859673419871030619925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174052959129119656081653133 65269859673419871030619925)
                    ·
                      refine ⟨3059524672191556454560309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65269859673419871030619925 3059524672191556454560309)
                      ·
                        rfl

theorem cell23_5958403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_5958403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958403 prefixEnd_5958403 := by exact prefixLift 5958403
  have htrace : WordTrace (prefixWord ++ tailWord_5958403) baseStart_5958403 baseEnd_5958403 := by
    simpa [prefixWord, tailWord_5958403, baseEnd_5958403] using wordTrace_append hprefix tailTrace_5958403
  have hstable : (prefixWord ++ tailWord_5958403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958403).length < 2 ^ (prefixWord ++ tailWord_5958403).sum := by decide
  have hdescent : baseEnd_5958403 < baseStart_5958403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958410 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_5958410 : Nat := 118140960795 + 5958410 * 2 ^ 59
def prefixEnd_5958410 : Nat := 4983230072969 + 3 ^ 40 * 5958410 * 2
def baseEnd_5958410 : Nat := 3059528266556137927172777

theorem tailTrace_5958410 : CollatzResearch.WordTrace tailWord_5958410 prefixEnd_5958410 3059528266556137927172777 := by
  unfold tailWord_5958410
  simp only [CollatzResearch.WordTrace]
  refine ⟨54330266585926415064152171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144880710895803773504405789 54330266585926415064152171)
  ·
    refine ⟨81495399878889622596228257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54330266585926415064152171 81495399878889622596228257)
    ·
      refine ⟨61121549909167216947171193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81495399878889622596228257 61121549909167216947171193)
      ·
        refine ⟨45841162431875412710378395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61121549909167216947171193 45841162431875412710378395)
        ·
          refine ⟨68761743647813119065567593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45841162431875412710378395 68761743647813119065567593)
          ·
            refine ⟨51571307735859839299175695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68761743647813119065567593 51571307735859839299175695)
            ·
              refine ⟨77356961603789758948763543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51571307735859839299175695 77356961603789758948763543)
              ·
                refine ⟨116035442405684638423145315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77356961603789758948763543 116035442405684638423145315)
                ·
                  refine ⟨174053163608526957634717973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116035442405684638423145315 174053163608526957634717973)
                  ·
                    refine ⟨8158742044149701139127405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 174053163608526957634717973 8158742044149701139127405)
                    ·
                      refine ⟨3059528266556137927172777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8158742044149701139127405 3059528266556137927172777)
                      ·
                        rfl

theorem cell23_5958410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_5958410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958410 prefixEnd_5958410 := by exact prefixLift 5958410
  have htrace : WordTrace (prefixWord ++ tailWord_5958410) baseStart_5958410 baseEnd_5958410 := by
    simpa [prefixWord, tailWord_5958410, baseEnd_5958410] using wordTrace_append hprefix tailTrace_5958410
  have hstable : (prefixWord ++ tailWord_5958410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958410).length < 2 ^ (prefixWord ++ tailWord_5958410).sum := by decide
  have hdescent : baseEnd_5958410 < baseStart_5958410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958458 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2]
def baseStart_5958458 : Nat := 118140960795 + 5958458 * 2 ^ 59
def prefixEnd_5958458 : Nat := 4983230072969 + 3 ^ 40 * 5958458 * 2
def baseEnd_5958458 : Nat := 3059552913627553739372557

theorem tailTrace_5958458 : CollatzResearch.WordTrace tailWord_5958458 prefixEnd_5958458 3059552913627553739372557 := by
  unfold tailWord_5958458
  simp only [CollatzResearch.WordTrace]
  refine ⟨54330704261882941113589007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144881878031687842969570685 54330704261882941113589007)
  ·
    refine ⟨81496056392824411670383511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54330704261882941113589007 81496056392824411670383511)
    ·
      refine ⟨122244084589236617505575267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81496056392824411670383511 122244084589236617505575267)
      ·
        refine ⟨183366126883854926258362901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122244084589236617505575267 183366126883854926258362901)
        ·
          refine ⟨8595287197680699668360761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183366126883854926258362901 8595287197680699668360761)
          ·
            refine ⟨6446465398260524751270571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8595287197680699668360761 6446465398260524751270571)
            ·
              refine ⟨9669698097390787126905857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6446465398260524751270571 9669698097390787126905857)
              ·
                refine ⟨7252273573043090345179393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9669698097390787126905857 7252273573043090345179393)
                ·
                  refine ⟨5439205179782317758884545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7252273573043090345179393 5439205179782317758884545)
                  ·
                    refine ⟨4079403884836738319163409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5439205179782317758884545 4079403884836738319163409)
                    ·
                      refine ⟨3059552913627553739372557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079403884836738319163409 3059552913627553739372557)
                      ·
                        rfl

theorem cell23_5958458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_5958458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958458 prefixEnd_5958458 := by exact prefixLift 5958458
  have htrace : WordTrace (prefixWord ++ tailWord_5958458) baseStart_5958458 baseEnd_5958458 := by
    simpa [prefixWord, tailWord_5958458, baseEnd_5958458] using wordTrace_append hprefix tailTrace_5958458
  have hstable : (prefixWord ++ tailWord_5958458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958458).length < 2 ^ (prefixWord ++ tailWord_5958458).sum := by decide
  have hdescent : baseEnd_5958458 < baseStart_5958458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958460 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_5958460 : Nat := 118140960795 + 5958460 * 2 ^ 59
def prefixEnd_5958460 : Nat := 4983230072969 + 3 ^ 40 * 5958460 * 2
def baseEnd_5958460 : Nat := 1019851313529620910515849

theorem tailTrace_5958460 : CollatzResearch.WordTrace tailWord_5958460 prefixEnd_5958460 1019851313529620910515849 := by
  unfold tailWord_5958460
  simp only [CollatzResearch.WordTrace]
  refine ⟨108661444996762259397964417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144881926662349679197285889 108661444996762259397964417)
  ·
    refine ⟨81496083747571694548473313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108661444996762259397964417 81496083747571694548473313)
    ·
      refine ⟨61122062810678770911354985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81496083747571694548473313 61122062810678770911354985)
      ·
        refine ⟨45841547108009078183516239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61122062810678770911354985 45841547108009078183516239)
        ·
          refine ⟨68762320662013617275274359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45841547108009078183516239 68762320662013617275274359)
          ·
            refine ⟨103143480993020425912911539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68762320662013617275274359 103143480993020425912911539)
            ·
              refine ⟨154715221489530638869367309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103143480993020425912911539 154715221489530638869367309)
              ·
                refine ⟨58018208058573989576012741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154715221489530638869367309 58018208058573989576012741)
                ·
                  refine ⟨10878414010982623045502389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58018208058573989576012741 10878414010982623045502389)
                  ·
                    refine ⟨1019851313529620910515849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10878414010982623045502389 1019851313529620910515849)
                    ·
                      rfl

theorem cell23_5958460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_5958460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958460 prefixEnd_5958460 := by exact prefixLift 5958460
  have htrace : WordTrace (prefixWord ++ tailWord_5958460) baseStart_5958460 baseEnd_5958460 := by
    simpa [prefixWord, tailWord_5958460, baseEnd_5958460] using wordTrace_append hprefix tailTrace_5958460
  have hstable : (prefixWord ++ tailWord_5958460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958460).length < 2 ^ (prefixWord ++ tailWord_5958460).sum := by decide
  have hdescent : baseEnd_5958460 < baseStart_5958460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958480 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_5958480 : Nat := 118140960795 + 5958480 * 2 ^ 59
def prefixEnd_5958480 : Nat := 4983230072969 + 3 ^ 40 * 5958480 * 2
def baseEnd_5958480 : Nat := 3059564210201952653297455

theorem tailTrace_5958480 : CollatzResearch.WordTrace tailWord_5958480 prefixEnd_5958480 3059564210201952653297455 := by
  unfold tailWord_5958480
  simp only [CollatzResearch.WordTrace]
  refine ⟨108661809726726031105828447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144882412968968041474437929 108661809726726031105828447)
  ·
    refine ⟨162992714590089046658742671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108661809726726031105828447 162992714590089046658742671)
    ·
      refine ⟨244489071885133569988114007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162992714590089046658742671 244489071885133569988114007)
      ·
        refine ⟨366733607827700354982171011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244489071885133569988114007 366733607827700354982171011)
        ·
          refine ⟨550100411741550532473256517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366733607827700354982171011 550100411741550532473256517)
          ·
            refine ⟨103143827201540724838735597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 550100411741550532473256517 103143827201540724838735597)
            ·
              refine ⟨38678935200577771814525849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103143827201540724838735597 38678935200577771814525849)
              ·
                refine ⟨29009201400433328860894387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38678935200577771814525849 29009201400433328860894387)
                ·
                  refine ⟨43513802100649993291341581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29009201400433328860894387 43513802100649993291341581)
                  ·
                    refine ⟨16317675787743747484253093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43513802100649993291341581 16317675787743747484253093)
                    ·
                      refine ⟨3059564210201952653297455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16317675787743747484253093 3059564210201952653297455)
                      ·
                        rfl

theorem cell23_5958480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_5958480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958480 prefixEnd_5958480 := by exact prefixLift 5958480
  have htrace : WordTrace (prefixWord ++ tailWord_5958480) baseStart_5958480 baseEnd_5958480 := by
    simpa [prefixWord, tailWord_5958480, baseEnd_5958480] using wordTrace_append hprefix tailTrace_5958480
  have hstable : (prefixWord ++ tailWord_5958480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958480).length < 2 ^ (prefixWord ++ tailWord_5958480).sum := by decide
  have hdescent : baseEnd_5958480 < baseStart_5958480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958497 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_5958497 : Nat := 118140960795 + 5958497 * 2 ^ 59
def prefixEnd_5958497 : Nat := 4983230072969 + 3 ^ 40 * 5958497 * 2
def baseEnd_5958497 : Nat := 3059572939373079086784877

theorem tailTrace_5958497 : CollatzResearch.WordTrace tailWord_5958497 prefixEnd_5958497 3059572939373079086784877 := by
  unfold tailWord_5958497
  simp only [CollatzResearch.WordTrace]
  refine ⟨217324239494390474115025745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144882826329593649410017163 217324239494390474115025745)
  ·
    refine ⟨162993179620792855586269309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217324239494390474115025745 162993179620792855586269309)
    ·
      refine ⟨61122442357797320844850991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162993179620792855586269309 61122442357797320844850991)
      ·
        refine ⟨91683663536695981267276487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61122442357797320844850991 91683663536695981267276487)
        ·
          refine ⟨137525495305043971900914731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91683663536695981267276487 137525495305043971900914731)
          ·
            refine ⟨206288242957565957851372097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137525495305043971900914731 206288242957565957851372097)
            ·
              refine ⟨154716182218174468388529073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206288242957565957851372097 154716182218174468388529073)
              ·
                refine ⟨116037136663630851291396805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154716182218174468388529073 116037136663630851291396805)
                ·
                  refine ⟨21756963124430784617136901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116037136663630851291396805 21756963124430784617136901)
                  ·
                    refine ⟨4079430585830772115713169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21756963124430784617136901 4079430585830772115713169)
                    ·
                      refine ⟨3059572939373079086784877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079430585830772115713169 3059572939373079086784877)
                      ·
                        rfl

theorem cell23_5958497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_5958497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958497 prefixEnd_5958497 := by exact prefixLift 5958497
  have htrace : WordTrace (prefixWord ++ tailWord_5958497) baseStart_5958497 baseEnd_5958497 := by
    simpa [prefixWord, tailWord_5958497, baseEnd_5958497] using wordTrace_append hprefix tailTrace_5958497
  have hstable : (prefixWord ++ tailWord_5958497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958497).length < 2 ^ (prefixWord ++ tailWord_5958497).sum := by decide
  have hdescent : baseEnd_5958497 < baseStart_5958497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958498 : List Nat := [3, 3, 2, 1, 4, 1, 1, 3, 5]
def baseStart_5958498 : Nat := 118140960795 + 5958498 * 2 ^ 59
def prefixEnd_5958498 : Nat := 4983230072969 + 3 ^ 40 * 5958498 * 2
def baseEnd_5958498 : Nat := 339952605872637064763597

theorem tailTrace_5958498 : CollatzResearch.WordTrace tailWord_5958498 prefixEnd_5958498 339952605872637064763597 := by
  unfold tailWord_5958498
  simp only [CollatzResearch.WordTrace]
  refine ⟨54331068991846712821453037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144882850644924567523874765 54331068991846712821453037)
  ·
    refine ⟨20374150871942517308044889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54331068991846712821453037 20374150871942517308044889)
    ·
      refine ⟨15280613153956887981033667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20374150871942517308044889 15280613153956887981033667)
      ·
        refine ⟨22920919730935331971550501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15280613153956887981033667 22920919730935331971550501)
        ·
          refine ⟨4297672449550374744665719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22920919730935331971550501 4297672449550374744665719)
          ·
            refine ⟨6446508674325562116998579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297672449550374744665719 6446508674325562116998579)
            ·
              refine ⟨9669763011488343175497869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6446508674325562116998579 9669763011488343175497869)
              ·
                refine ⟨3626161129308128690811701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9669763011488343175497869 3626161129308128690811701)
                ·
                  refine ⟨339952605872637064763597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3626161129308128690811701 339952605872637064763597)
                  ·
                    rfl

theorem cell23_5958498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_5958498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958498 prefixEnd_5958498 := by exact prefixLift 5958498
  have htrace : WordTrace (prefixWord ++ tailWord_5958498) baseStart_5958498 baseEnd_5958498 := by
    simpa [prefixWord, tailWord_5958498, baseEnd_5958498] using wordTrace_append hprefix tailTrace_5958498
  have hstable : (prefixWord ++ tailWord_5958498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958498).length < 2 ^ (prefixWord ++ tailWord_5958498).sum := by decide
  have hdescent : baseEnd_5958498 < baseStart_5958498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958524 : List Nat := [2, 2, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_5958524 : Nat := 118140960795 + 5958524 * 2 ^ 59
def prefixEnd_5958524 : Nat := 4983230072969 + 3 ^ 40 * 5958524 * 2
def baseEnd_5958524 : Nat := 1019862267783583493715751

theorem tailTrace_5958524 : CollatzResearch.WordTrace tailWord_5958524 prefixEnd_5958524 1019862267783583493715751 := by
  unfold tailWord_5958524
  simp only [CollatzResearch.WordTrace]
  refine ⟨108662612132646328863129313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144883482843528438484172417 108662612132646328863129313)
  ·
    refine ⟨81496959099484746647346985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108662612132646328863129313 81496959099484746647346985)
    ·
      refine ⟨61122719324613559985510239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81496959099484746647346985 61122719324613559985510239)
      ·
        refine ⟨91684078986920339978265359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61122719324613559985510239 91684078986920339978265359)
        ·
          refine ⟨137526118480380509967398039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91684078986920339978265359 137526118480380509967398039)
          ·
            refine ⟨206289177720570764951097059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137526118480380509967398039 206289177720570764951097059)
            ·
              refine ⟨309433766580856147426645589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206289177720570764951097059 309433766580856147426645589)
              ·
                refine ⟨3626176952119407977656003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 309433766580856147426645589 3626176952119407977656003)
                ·
                  refine ⟨5439265428179111966484005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626176952119407977656003 5439265428179111966484005)
                  ·
                    refine ⟨1019862267783583493715751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5439265428179111966484005 1019862267783583493715751)
                    ·
                      rfl

theorem cell23_5958524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_5958524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958524 prefixEnd_5958524 := by exact prefixLift 5958524
  have htrace : WordTrace (prefixWord ++ tailWord_5958524) baseStart_5958524 baseEnd_5958524 := by
    simpa [prefixWord, tailWord_5958524, baseEnd_5958524] using wordTrace_append hprefix tailTrace_5958524
  have hstable : (prefixWord ++ tailWord_5958524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958524).length < 2 ^ (prefixWord ++ tailWord_5958524).sum := by decide
  have hdescent : baseEnd_5958524 < baseStart_5958524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958537 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 6]
def baseStart_5958537 : Nat := 118140960795 + 5958537 * 2 ^ 59
def prefixEnd_5958537 : Nat := 4983230072969 + 3 ^ 40 * 5958537 * 2
def baseEnd_5958537 : Nat := 339954830955473214476077

theorem tailTrace_5958537 : CollatzResearch.WordTrace tailWord_5958537 prefixEnd_5958537 339954830955473214476077 := by
  unfold tailWord_5958537
  simp only [CollatzResearch.WordTrace]
  refine ⟨217325698414245560946481865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144883798942830373964321243 217325698414245560946481865)
  ·
    refine ⟨162994273810684170709861399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217325698414245560946481865 162994273810684170709861399)
    ·
      refine ⟨244491410716026256064792099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162994273810684170709861399 244491410716026256064792099)
      ·
        refine ⟨366737116074039384097188149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244491410716026256064792099 366737116074039384097188149)
        ·
          refine ⟨34381604631941192259111389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 366737116074039384097188149 34381604631941192259111389)
          ·
            refine ⟨12893101736977947097166771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34381604631941192259111389 12893101736977947097166771)
            ·
              refine ⟨19339652605466920645750157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12893101736977947097166771 19339652605466920645750157)
              ·
                refine ⟨7252369727050095242156309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19339652605466920645750157 7252369727050095242156309)
                ·
                  refine ⟨339954830955473214476077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7252369727050095242156309 339954830955473214476077)
                  ·
                    rfl

theorem cell23_5958537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 6].length) (baseStart_5958537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958537 prefixEnd_5958537 := by exact prefixLift 5958537
  have htrace : WordTrace (prefixWord ++ tailWord_5958537) baseStart_5958537 baseEnd_5958537 := by
    simpa [prefixWord, tailWord_5958537, baseEnd_5958537] using wordTrace_append hprefix tailTrace_5958537
  have hstable : (prefixWord ++ tailWord_5958537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958537).length < 2 ^ (prefixWord ++ tailWord_5958537).sum := by decide
  have hdescent : baseEnd_5958537 < baseStart_5958537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958540 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_5958540 : Nat := 118140960795 + 5958540 * 2 ^ 59
def prefixEnd_5958540 : Nat := 4983230072969 + 3 ^ 40 * 5958540 * 2
def baseEnd_5958540 : Nat := 3059595019041222418547179

theorem tailTrace_5958540 : CollatzResearch.WordTrace tailWord_5958540 prefixEnd_5958540 3059595019041222418547179 := by
  unfold tailWord_5958540
  simp only [CollatzResearch.WordTrace]
  refine ⟨108662903916617346229420537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144883871888823128305894049 108662903916617346229420537)
  ·
    refine ⟨81497177937463009672065403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108662903916617346229420537 81497177937463009672065403)
    ·
      refine ⟨122245766906194514508098105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81497177937463009672065403 122245766906194514508098105)
      ·
        refine ⟨91684325179645885881073579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122245766906194514508098105 91684325179645885881073579)
        ·
          refine ⟨137526487769468828821610369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91684325179645885881073579 137526487769468828821610369)
          ·
            refine ⟨103144865827101621616207777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137526487769468828821610369 103144865827101621616207777)
            ·
              refine ⟨77358649370326216212155833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103144865827101621616207777 77358649370326216212155833)
              ·
                refine ⟨58018987027744662159116875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77358649370326216212155833 58018987027744662159116875)
                ·
                  refine ⟨87028480541616993238675313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58018987027744662159116875 87028480541616993238675313)
                  ·
                    refine ⟨65271360406212744929006485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87028480541616993238675313 65271360406212744929006485)
                    ·
                      refine ⟨3059595019041222418547179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65271360406212744929006485 3059595019041222418547179)
                      ·
                        rfl

theorem cell23_5958540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_5958540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958540 prefixEnd_5958540 := by exact prefixLift 5958540
  have htrace : WordTrace (prefixWord ++ tailWord_5958540) baseStart_5958540 baseEnd_5958540 := by
    simpa [prefixWord, tailWord_5958540, baseEnd_5958540] using wordTrace_append hprefix tailTrace_5958540
  have hstable : (prefixWord ++ tailWord_5958540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958540).length < 2 ^ (prefixWord ++ tailWord_5958540).sum := by decide
  have hdescent : baseEnd_5958540 < baseStart_5958540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958604 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_5958604 : Nat := 118140960795 + 5958604 * 2 ^ 59
def prefixEnd_5958604 : Nat := 4983230072969 + 3 ^ 40 * 5958604 * 2
def baseEnd_5958604 : Nat := 3059627881803110168146885

theorem tailTrace_5958604 : CollatzResearch.WordTrace tailWord_5958604 prefixEnd_5958604 3059627881803110168146885 := by
  unfold tailWord_5958604
  simp only [CollatzResearch.WordTrace]
  refine ⟨108664071052501415694585433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144885428070001887592780577 108664071052501415694585433)
  ·
    refine ⟨81498053289376061770939075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108664071052501415694585433 81498053289376061770939075)
    ·
      refine ⟨122247079934064092656408613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81498053289376061770939075 122247079934064092656408613)
      ·
        refine ⟨22921327487637017373076615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122247079934064092656408613 22921327487637017373076615)
        ·
          refine ⟨34381991231455526059614923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22921327487637017373076615 34381991231455526059614923)
          ·
            refine ⟨51572986847183289089422385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34381991231455526059614923 51572986847183289089422385)
            ·
              refine ⟨38679740135387466817066789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51572986847183289089422385 38679740135387466817066789)
              ·
                refine ⟨7252451275385150028200023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38679740135387466817066789 7252451275385150028200023)
                ·
                  refine ⟨10878676913077725042300035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7252451275385150028200023 10878676913077725042300035)
                  ·
                    refine ⟨16318015369616587563450053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10878676913077725042300035 16318015369616587563450053)
                    ·
                      refine ⟨3059627881803110168146885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16318015369616587563450053 3059627881803110168146885)
                      ·
                        rfl

theorem cell23_5958604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_5958604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958604 prefixEnd_5958604 := by exact prefixLift 5958604
  have htrace : WordTrace (prefixWord ++ tailWord_5958604) baseStart_5958604 baseEnd_5958604 := by
    simpa [prefixWord, tailWord_5958604, baseEnd_5958604] using wordTrace_append hprefix tailTrace_5958604
  have hstable : (prefixWord ++ tailWord_5958604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958604).length < 2 ^ (prefixWord ++ tailWord_5958604).sum := by decide
  have hdescent : baseEnd_5958604 < baseStart_5958604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958621 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5958621 : Nat := 118140960795 + 5958621 * 2 ^ 59
def prefixEnd_5958621 : Nat := 4983230072969 + 3 ^ 40 * 5958621 * 2
def baseEnd_5958621 : Nat := 3059636610974236601634307

theorem tailTrace_5958621 : CollatzResearch.WordTrace tailWord_5958621 prefixEnd_5958621 3059636610974236601634307 := by
  unfold tailWord_5958621
  simp only [CollatzResearch.WordTrace]
  refine ⟨217328762145941243292539717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144885841430627495528359811 217328762145941243292539717)
  ·
    refine ⟨40749142902363983117351197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217328762145941243292539717 40749142902363983117351197)
    ·
      refine ⟨15280928588386493669006699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40749142902363983117351197 15280928588386493669006699)
      ·
        refine ⟨22921392882579740503510049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15280928588386493669006699 22921392882579740503510049)
        ·
          refine ⟨17191044661934805377632537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22921392882579740503510049 17191044661934805377632537)
          ·
            refine ⟨12893283496451104033224403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17191044661934805377632537 12893283496451104033224403)
            ·
              refine ⟨19339925244676656049836605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12893283496451104033224403 19339925244676656049836605)
              ·
                refine ⟨7252471966753746018688727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19339925244676656049836605 7252471966753746018688727)
                ·
                  refine ⟨10878707950130619028033091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7252471966753746018688727 10878707950130619028033091)
                  ·
                    refine ⟨16318061925195928542049637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10878707950130619028033091 16318061925195928542049637)
                    ·
                      refine ⟨3059636610974236601634307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16318061925195928542049637 3059636610974236601634307)
                      ·
                        rfl

theorem cell23_5958621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5958621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958621 prefixEnd_5958621 := by exact prefixLift 5958621
  have htrace : WordTrace (prefixWord ++ tailWord_5958621) baseStart_5958621 baseEnd_5958621 := by
    simpa [prefixWord, tailWord_5958621, baseEnd_5958621] using wordTrace_append hprefix tailTrace_5958621
  have hstable : (prefixWord ++ tailWord_5958621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958621).length < 2 ^ (prefixWord ++ tailWord_5958621).sum := by decide
  have hdescent : baseEnd_5958621 < baseStart_5958621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958631 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 2, 4]
def baseStart_5958631 : Nat := 118140960795 + 5958631 * 2 ^ 59
def prefixEnd_5958631 : Nat := 4983230072969 + 3 ^ 40 * 5958631 * 2
def baseEnd_5958631 : Nat := 1019880581926927187503087

theorem tailTrace_5958631 : CollatzResearch.WordTrace tailWord_5958631 prefixEnd_5958631 1019880581926927187503087 := by
  unfold tailWord_5958631
  simp only [CollatzResearch.WordTrace]
  refine ⟨217329126875905015000403747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144886084583936676666935831 217329126875905015000403747)
  ·
    refine ⟨325993690313857522500605621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217329126875905015000403747 325993690313857522500605621)
    ·
      refine ⟨30561908466924142734431777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 325993690313857522500605621 30561908466924142734431777)
      ·
        refine ⟨22921431350193107050823833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30561908466924142734431777 22921431350193107050823833)
        ·
          refine ⟨17191073512644830288117875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22921431350193107050823833 17191073512644830288117875)
          ·
            refine ⟨25786610268967245432176813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17191073512644830288117875 25786610268967245432176813)
            ·
              refine ⟨9669978850862717037066305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25786610268967245432176813 9669978850862717037066305)
              ·
                refine ⟨7252484138147037777799729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9669978850862717037066305 7252484138147037777799729)
                ·
                  refine ⟨5439363103610278333349797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7252484138147037777799729 5439363103610278333349797)
                  ·
                    refine ⟨1019880581926927187503087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5439363103610278333349797 1019880581926927187503087)
                    ·
                      rfl

theorem cell23_5958631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_5958631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958631 prefixEnd_5958631 := by exact prefixLift 5958631
  have htrace : WordTrace (prefixWord ++ tailWord_5958631) baseStart_5958631 baseEnd_5958631 := by
    simpa [prefixWord, tailWord_5958631, baseEnd_5958631] using wordTrace_append hprefix tailTrace_5958631
  have hstable : (prefixWord ++ tailWord_5958631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958631).length < 2 ^ (prefixWord ++ tailWord_5958631).sum := by decide
  have hdescent : baseEnd_5958631 < baseStart_5958631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958667 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5]
def baseStart_5958667 : Nat := 118140960795 + 5958667 * 2 ^ 59
def prefixEnd_5958667 : Nat := 4983230072969 + 3 ^ 40 * 5958667 * 2
def baseEnd_5958667 : Nat := 3059660231084343421659095

theorem tailTrace_5958667 : CollatzResearch.WordTrace tailWord_5958667 prefixEnd_5958667 3059660231084343421659095 := by
  unfold tailWord_5958667
  simp only [CollatzResearch.WordTrace]
  refine ⟨217330439903774593148714255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144886959935849728765809503 217330439903774593148714255)
  ·
    refine ⟨325995659855661889723071383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217330439903774593148714255 325995659855661889723071383)
    ·
      refine ⟨488993489783492834584607075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325995659855661889723071383 488993489783492834584607075)
      ·
        refine ⟨733490234675239251876910613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488993489783492834584607075 733490234675239251876910613)
        ·
          refine ⟨34382354750401839931730185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 733490234675239251876910613 34382354750401839931730185)
          ·
            refine ⟨25786766062801379948797639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34382354750401839931730185 25786766062801379948797639)
            ·
              refine ⟨38680149094202069923196459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25786766062801379948797639 38680149094202069923196459)
              ·
                refine ⟨58020223641303104884794689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38680149094202069923196459 58020223641303104884794689)
                ·
                  refine ⟨43515167730977328663596017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58020223641303104884794689 43515167730977328663596017)
                  ·
                    refine ⟨32636375798232996497697013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43515167730977328663596017 32636375798232996497697013)
                    ·
                      refine ⟨3059660231084343421659095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32636375798232996497697013 3059660231084343421659095)
                      ·
                        rfl

theorem cell23_5958667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_5958667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958667 prefixEnd_5958667 := by exact prefixLift 5958667
  have htrace : WordTrace (prefixWord ++ tailWord_5958667) baseStart_5958667 baseEnd_5958667 := by
    simpa [prefixWord, tailWord_5958667, baseEnd_5958667] using wordTrace_append hprefix tailTrace_5958667
  have hstable : (prefixWord ++ tailWord_5958667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958667).length < 2 ^ (prefixWord ++ tailWord_5958667).sum := by decide
  have hdescent : baseEnd_5958667 < baseStart_5958667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958681 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 1, 3, 2]
def baseStart_5958681 : Nat := 118140960795 + 5958681 * 2 ^ 59
def prefixEnd_5958681 : Nat := 4983230072969 + 3 ^ 40 * 5958681 * 2
def baseEnd_5958681 : Nat := 3059667419813506366884031

theorem tailTrace_5958681 : CollatzResearch.WordTrace tailWord_5958681 prefixEnd_5958681 3059667419813506366884031 := by
  unfold tailWord_5958681
  simp only [CollatzResearch.WordTrace]
  refine ⟨217330950525723873539723897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144887300350482582359815931 217330950525723873539723897)
  ·
    refine ⟨162998212894292905154792923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217330950525723873539723897 162998212894292905154792923)
    ·
      refine ⟨244497319341439357732189385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162998212894292905154792923 244497319341439357732189385)
      ·
        refine ⟨183372989506079518299142039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244497319341439357732189385 183372989506079518299142039)
        ·
          refine ⟨275059484259119277448713059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183372989506079518299142039 275059484259119277448713059)
          ·
            refine ⟨412589226388678916173069589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275059484259119277448713059 412589226388678916173069589)
            ·
              refine ⟨19340119986969324195612637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 412589226388678916173069589 19340119986969324195612637)
              ·
                refine ⟨7252544995113496573354739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19340119986969324195612637 7252544995113496573354739)
                ·
                  refine ⟨10878817492670244860032109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7252544995113496573354739 10878817492670244860032109)
                  ·
                    refine ⟨4079556559751341822512041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10878817492670244860032109 4079556559751341822512041)
                    ·
                      refine ⟨3059667419813506366884031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079556559751341822512041 3059667419813506366884031)
                      ·
                        rfl

theorem cell23_5958681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_5958681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958681 prefixEnd_5958681 := by exact prefixLift 5958681
  have htrace : WordTrace (prefixWord ++ tailWord_5958681) baseStart_5958681 baseEnd_5958681 := by
    simpa [prefixWord, tailWord_5958681, baseEnd_5958681] using wordTrace_append hprefix tailTrace_5958681
  have hstable : (prefixWord ++ tailWord_5958681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958681).length < 2 ^ (prefixWord ++ tailWord_5958681).sum := by decide
  have hdescent : baseEnd_5958681 < baseStart_5958681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958707 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4]
def baseStart_5958707 : Nat := 118140960795 + 5958707 * 2 ^ 59
def prefixEnd_5958707 : Nat := 4983230072969 + 3 ^ 40 * 5958707 * 2
def baseEnd_5958707 : Nat := 3059680770310523265158911

theorem tailTrace_5958707 : CollatzResearch.WordTrace tailWord_5958707 prefixEnd_5958707 3059680770310523265158911 := by
  unfold tailWord_5958707
  simp only [CollatzResearch.WordTrace]
  refine ⟨217331898823629679980170375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144887932549086453320113583 217331898823629679980170375)
  ·
    refine ⟨325997848235444519970255563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217331898823629679980170375 325997848235444519970255563)
    ·
      refine ⟨488996772353166779955383345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325997848235444519970255563 488996772353166779955383345)
      ·
        refine ⟨366747579264875084966537509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488996772353166779955383345 366747579264875084966537509)
        ·
          refine ⟨68765171112164078431225783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366747579264875084966537509 68765171112164078431225783)
          ·
            refine ⟨103147756668246117646838675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68765171112164078431225783 103147756668246117646838675)
            ·
              refine ⟨154721635002369176470258013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103147756668246117646838675 154721635002369176470258013)
              ·
                refine ⟨58020613125888441176346755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154721635002369176470258013 58020613125888441176346755)
                ·
                  refine ⟨87030919688832661764520133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58020613125888441176346755 87030919688832661764520133)
                  ·
                    refine ⟨16318297441656124080847525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87030919688832661764520133 16318297441656124080847525)
                    ·
                      refine ⟨3059680770310523265158911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16318297441656124080847525 3059680770310523265158911)
                      ·
                        rfl

theorem cell23_5958707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_5958707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958707 prefixEnd_5958707 := by exact prefixLift 5958707
  have htrace : WordTrace (prefixWord ++ tailWord_5958707) baseStart_5958707 baseEnd_5958707 := by
    simpa [prefixWord, tailWord_5958707, baseEnd_5958707] using wordTrace_append hprefix tailTrace_5958707
  have hstable : (prefixWord ++ tailWord_5958707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958707).length < 2 ^ (prefixWord ++ tailWord_5958707).sum := by decide
  have hdescent : baseEnd_5958707 < baseStart_5958707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958744 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_5958744 : Nat := 118140960795 + 5958744 * 2 ^ 59
def prefixEnd_5958744 : Nat := 4983230072969 + 3 ^ 40 * 5958744 * 2
def baseEnd_5958744 : Nat := 3059699769094739620396241

theorem tailTrace_5958744 : CollatzResearch.WordTrace tailWord_5958744 prefixEnd_5958744 3059699769094739620396241 := by
  unfold tailWord_5958744
  simp only [CollatzResearch.WordTrace]
  refine ⟨108666624162247817649633643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144888832216330423532844857 108666624162247817649633643)
  ·
    refine ⟨162999936243371726474450465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108666624162247817649633643 162999936243371726474450465)
    ·
      refine ⟨122249952182528794855837849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162999936243371726474450465 122249952182528794855837849)
      ·
        refine ⟨91687464136896596141878387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122249952182528794855837849 91687464136896596141878387)
        ·
          refine ⟨137531196205344894212817581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91687464136896596141878387 137531196205344894212817581)
          ·
            refine ⟨51574198577004335329806593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137531196205344894212817581 51574198577004335329806593)
            ·
              refine ⟨38680648932753251497354945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51574198577004335329806593 38680648932753251497354945)
              ·
                refine ⟨29010486699564938623016209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38680648932753251497354945 29010486699564938623016209)
                ·
                  refine ⟨21757865024673703967262157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29010486699564938623016209 21757865024673703967262157)
                  ·
                    refine ⟨8159199384252638987723309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21757865024673703967262157 8159199384252638987723309)
                    ·
                      refine ⟨3059699769094739620396241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8159199384252638987723309 3059699769094739620396241)
                      ·
                        rfl

theorem cell23_5958744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_5958744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958744 prefixEnd_5958744 := by exact prefixLift 5958744
  have htrace : WordTrace (prefixWord ++ tailWord_5958744) baseStart_5958744 baseEnd_5958744 := by
    simpa [prefixWord, tailWord_5958744, baseEnd_5958744] using wordTrace_append hprefix tailTrace_5958744
  have hstable : (prefixWord ++ tailWord_5958744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958744).length < 2 ^ (prefixWord ++ tailWord_5958744).sum := by decide
  have hdescent : baseEnd_5958744 < baseStart_5958744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958862 : List Nat := [4, 1, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_5958862 : Nat := 118140960795 + 5958862 * 2 ^ 59
def prefixEnd_5958862 : Nat := 4983230072969 + 3 ^ 40 * 5958862 * 2
def baseEnd_5958862 : Nat := 1019920119937323386240233

theorem tailTrace_5958862 : CollatzResearch.WordTrace tailWord_5958862 prefixEnd_5958862 1019920119937323386240233 := by
  unfold tailWord_5958862
  simp only [CollatzResearch.WordTrace]
  refine ⟨27167194017258517681507855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144891701425378760968041893 27167194017258517681507855)
  ·
    refine ⟨40750791025887776522261783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27167194017258517681507855 40750791025887776522261783)
    ·
      refine ⟨61126186538831664783392675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40750791025887776522261783 61126186538831664783392675)
      ·
        refine ⟨91689279808247497175089013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61126186538831664783392675 91689279808247497175089013)
        ·
          refine ⟨8595869982023202860164595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91689279808247497175089013 8595869982023202860164595)
          ·
            refine ⟨12893804973034804290246893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8595869982023202860164595 12893804973034804290246893)
            ·
              refine ⟨4835176864888051608842585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12893804973034804290246893 4835176864888051608842585)
              ·
                refine ⟨3626382648666038706631939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4835176864888051608842585 3626382648666038706631939)
                ·
                  refine ⟨5439573972999058059947909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626382648666038706631939 5439573972999058059947909)
                  ·
                    refine ⟨1019920119937323386240233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5439573972999058059947909 1019920119937323386240233)
                    ·
                      rfl

theorem cell23_5958862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_5958862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958862 prefixEnd_5958862 := by exact prefixLift 5958862
  have htrace : WordTrace (prefixWord ++ tailWord_5958862) baseStart_5958862 baseEnd_5958862 := by
    simpa [prefixWord, tailWord_5958862, baseEnd_5958862] using wordTrace_append hprefix tailTrace_5958862
  have hstable : (prefixWord ++ tailWord_5958862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958862).length < 2 ^ (prefixWord ++ tailWord_5958862).sum := by decide
  have hdescent : baseEnd_5958862 < baseStart_5958862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958874 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_5958874 : Nat := 118140960795 + 5958874 * 2 ^ 59
def prefixEnd_5958874 : Nat := 4983230072969 + 3 ^ 40 * 5958874 * 2
def baseEnd_5958874 : Nat := 3059766521579824111770643

theorem tailTrace_5958874 : CollatzResearch.WordTrace tailWord_5958874 prefixEnd_5958874 3059766521579824111770643 := by
  unfold tailWord_5958874
  simp only [CollatzResearch.WordTrace]
  refine ⟨54334497453506166875374919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144891993209349778334333117 54334497453506166875374919)
  ·
    refine ⟨81501746180259250313062379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54334497453506166875374919 81501746180259250313062379)
    ·
      refine ⟨122252619270388875469593569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81501746180259250313062379 122252619270388875469593569)
      ·
        refine ⟨91689464452791656602195177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122252619270388875469593569 91689464452791656602195177)
        ·
          refine ⟨68767098339593742451646383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91689464452791656602195177 68767098339593742451646383)
          ·
            refine ⟨103150647509390613677469575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68767098339593742451646383 103150647509390613677469575)
            ·
              refine ⟨154725971264085920516204363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103150647509390613677469575 154725971264085920516204363)
              ·
                refine ⟨232088956896128880774306545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154725971264085920516204363 232088956896128880774306545)
                ·
                  refine ⟨174066717672096660580729909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232088956896128880774306545 174066717672096660580729909)
                  ·
                    refine ⟨16318754781759061929443429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174066717672096660580729909 16318754781759061929443429)
                    ·
                      refine ⟨3059766521579824111770643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16318754781759061929443429 3059766521579824111770643)
                      ·
                        rfl

theorem cell23_5958874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_5958874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958874 prefixEnd_5958874 := by exact prefixLift 5958874
  have htrace : WordTrace (prefixWord ++ tailWord_5958874) baseStart_5958874 baseEnd_5958874 := by
    simpa [prefixWord, tailWord_5958874, baseEnd_5958874] using wordTrace_append hprefix tailTrace_5958874
  have hstable : (prefixWord ++ tailWord_5958874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958874).length < 2 ^ (prefixWord ++ tailWord_5958874).sum := by decide
  have hdescent : baseEnd_5958874 < baseStart_5958874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958891 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 4]
def baseStart_5958891 : Nat := 118140960795 + 5958891 * 2 ^ 59
def prefixEnd_5958891 : Nat := 4983230072969 + 3 ^ 40 * 5958891 * 2
def baseEnd_5958891 : Nat := 3059775250750950545258065

theorem tailTrace_5958891 : CollatzResearch.WordTrace tailWord_5958891 prefixEnd_5958891 3059775250750950545258065 := by
  unfold tailWord_5958891
  simp only [CollatzResearch.WordTrace]
  refine ⟨217338609854963079404868527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144892406569975386269912351 217338609854963079404868527)
  ·
    refine ⟨326007914782444619107302791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217338609854963079404868527 326007914782444619107302791)
    ·
      refine ⟨489011872173666928660954187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326007914782444619107302791 489011872173666928660954187)
      ·
        refine ⟨733517808260500392991431281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489011872173666928660954187 733517808260500392991431281)
        ·
          refine ⟨550138356195375294743573461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733517808260500392991431281 550138356195375294743573461)
          ·
            refine ⟨12893867723329108470552503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 550138356195375294743573461 12893867723329108470552503)
            ·
              refine ⟨19340801584993662705828755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12893867723329108470552503 19340801584993662705828755)
              ·
                refine ⟨29011202377490494058743133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19340801584993662705828755 29011202377490494058743133)
                ·
                  refine ⟨10879200891558935272028675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29011202377490494058743133 10879200891558935272028675)
                  ·
                    refine ⟨16318801337338402908043013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10879200891558935272028675 16318801337338402908043013)
                    ·
                      refine ⟨3059775250750950545258065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16318801337338402908043013 3059775250750950545258065)
                      ·
                        rfl

theorem cell23_5958891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 4].length) (baseStart_5958891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958891 prefixEnd_5958891 := by exact prefixLift 5958891
  have htrace : WordTrace (prefixWord ++ tailWord_5958891) baseStart_5958891 baseEnd_5958891 := by
    simpa [prefixWord, tailWord_5958891, baseEnd_5958891] using wordTrace_append hprefix tailTrace_5958891
  have hstable : (prefixWord ++ tailWord_5958891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958891).length < 2 ^ (prefixWord ++ tailWord_5958891).sum := by decide
  have hdescent : baseEnd_5958891 < baseStart_5958891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958895 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 2, 3, 2]
def baseStart_5958895 : Nat := 118140960795 + 5958895 * 2 ^ 59
def prefixEnd_5958895 : Nat := 4983230072969 + 3 ^ 40 * 5958895 * 2
def baseEnd_5958895 : Nat := 3059777304673568529608047

theorem tailTrace_5958895 : CollatzResearch.WordTrace tailWord_5958895 prefixEnd_5958895 3059777304673568529608047 := by
  unfold tailWord_5958895
  simp only [CollatzResearch.WordTrace]
  refine ⟨217338755746948588088014139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144892503831299058725342759 217338755746948588088014139)
  ·
    refine ⟨326008133620422882132021209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217338755746948588088014139 326008133620422882132021209)
    ·
      refine ⟨244506100215317161599015907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326008133620422882132021209 244506100215317161599015907)
      ·
        refine ⟨366759150322975742398523861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244506100215317161599015907 366759150322975742398523861)
        ·
          refine ⟨8595917585694743962465403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 366759150322975742398523861 8595917585694743962465403)
          ·
            refine ⟨12893876378542115943698105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8595917585694743962465403 12893876378542115943698105)
            ·
              refine ⟨9670407283906586957773579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12893876378542115943698105 9670407283906586957773579)
              ·
                refine ⟨14505610925859880436660369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9670407283906586957773579 14505610925859880436660369)
                ·
                  refine ⟨10879208194394910327495277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14505610925859880436660369 10879208194394910327495277)
                  ·
                    refine ⟨4079703072898091372810729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10879208194394910327495277 4079703072898091372810729)
                    ·
                      refine ⟨3059777304673568529608047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079703072898091372810729 3059777304673568529608047)
                      ·
                        rfl

theorem cell23_5958895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3, 2].length) (baseStart_5958895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958895 prefixEnd_5958895 := by exact prefixLift 5958895
  have htrace : WordTrace (prefixWord ++ tailWord_5958895) baseStart_5958895 baseEnd_5958895 := by
    simpa [prefixWord, tailWord_5958895, baseEnd_5958895] using wordTrace_append hprefix tailTrace_5958895
  have hstable : (prefixWord ++ tailWord_5958895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958895).length < 2 ^ (prefixWord ++ tailWord_5958895).sum := by decide
  have hdescent : baseEnd_5958895 < baseStart_5958895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958911 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 5]
def baseStart_5958911 : Nat := 118140960795 + 5958911 * 2 ^ 59
def prefixEnd_5958911 : Nat := 4983230072969 + 3 ^ 40 * 5958911 * 2
def baseEnd_5958911 : Nat := 3059785520364040467007973

theorem tailTrace_5958911 : CollatzResearch.WordTrace tailWord_5958911 prefixEnd_5958911 3059785520364040467007973 := by
  unfold tailWord_5958911
  simp only [CollatzResearch.WordTrace]
  refine ⟨217339339314890622820596587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144892892876593748547064391 217339339314890622820596587)
  ·
    refine ⟨326009008972335934230894881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217339339314890622820596587 326009008972335934230894881)
    ·
      refine ⟨244506756729251950673171161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326009008972335934230894881 244506756729251950673171161)
      ·
        refine ⟨183380067546938963004878371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244506756729251950673171161 183380067546938963004878371)
        ·
          refine ⟨275070101320408444507317557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183380067546938963004878371 275070101320408444507317557)
          ·
            refine ⟨25787821998788291672561021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 275070101320408444507317557 25787821998788291672561021)
            ·
              refine ⟨9670433249545609377210383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25787821998788291672561021 9670433249545609377210383)
              ·
                refine ⟨14505649874318414065815575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9670433249545609377210383 14505649874318414065815575)
                ·
                  refine ⟨21758474811477621098723363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14505649874318414065815575 21758474811477621098723363)
                  ·
                    refine ⟨32637712217216431648085045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21758474811477621098723363 32637712217216431648085045)
                    ·
                      refine ⟨3059785520364040467007973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32637712217216431648085045 3059785520364040467007973)
                      ·
                        rfl

theorem cell23_5958911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_5958911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958911 prefixEnd_5958911 := by exact prefixLift 5958911
  have htrace : WordTrace (prefixWord ++ tailWord_5958911) baseStart_5958911 baseEnd_5958911 := by
    simpa [prefixWord, tailWord_5958911, baseEnd_5958911] using wordTrace_append hprefix tailTrace_5958911
  have hstable : (prefixWord ++ tailWord_5958911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958911).length < 2 ^ (prefixWord ++ tailWord_5958911).sum := by decide
  have hdescent : baseEnd_5958911 < baseStart_5958911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958938 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_5958938 : Nat := 118140960795 + 5958938 * 2 ^ 59
def prefixEnd_5958938 : Nat := 4983230072969 + 3 ^ 40 * 5958938 * 2
def baseEnd_5958938 : Nat := 3059799384341711861370349

theorem tailTrace_5958938 : CollatzResearch.WordTrace tailWord_5958938 prefixEnd_5958938 3059799384341711861370349 := by
  unfold tailWord_5958938
  simp only [CollatzResearch.WordTrace]
  refine ⟨54335081021448201607957367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144893549390528537621219645 54335081021448201607957367)
  ·
    refine ⟨81502621532172302411936051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54335081021448201607957367 81502621532172302411936051)
    ·
      refine ⟨122253932298258453617904077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81502621532172302411936051 122253932298258453617904077)
      ·
        refine ⟨45845224611846920106714029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122253932298258453617904077 45845224611846920106714029)
        ·
          refine ⟨17191959229442595040017761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45845224611846920106714029 17191959229442595040017761)
          ·
            refine ⟨12893969422081946280013321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17191959229442595040017761 12893969422081946280013321)
            ·
              refine ⟨9670477066561459710009991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12893969422081946280013321 9670477066561459710009991)
              ·
                refine ⟨14505715599842189565014987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9670477066561459710009991 14505715599842189565014987)
                ·
                  refine ⟨21758573399763284347522481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14505715599842189565014987 21758573399763284347522481)
                  ·
                    refine ⟨16318930049822463260641861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21758573399763284347522481 16318930049822463260641861)
                    ·
                      refine ⟨3059799384341711861370349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16318930049822463260641861 3059799384341711861370349)
                      ·
                        rfl

theorem cell23_5958938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_5958938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958938 prefixEnd_5958938 := by exact prefixLift 5958938
  have htrace : WordTrace (prefixWord ++ tailWord_5958938) baseStart_5958938 baseEnd_5958938 := by
    simpa [prefixWord, tailWord_5958938, baseEnd_5958938] using wordTrace_append hprefix tailTrace_5958938
  have hstable : (prefixWord ++ tailWord_5958938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958938).length < 2 ^ (prefixWord ++ tailWord_5958938).sum := by decide
  have hdescent : baseEnd_5958938 < baseStart_5958938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958962 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_5958962 : Nat := 118140960795 + 5958962 * 2 ^ 59
def prefixEnd_5958962 : Nat := 4983230072969 + 3 ^ 40 * 5958962 * 2
def baseEnd_5958962 : Nat := 3059811707877419767470239

theorem tailTrace_5958962 : CollatzResearch.WordTrace tailWord_5958962 prefixEnd_5958962 3059811707877419767470239 := by
  unfold tailWord_5958962
  simp only [CollatzResearch.WordTrace]
  refine ⟨54335299859426464632675785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144894132958470572353802093 54335299859426464632675785)
  ·
    refine ⟨40751474894569848474506839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54335299859426464632675785 40751474894569848474506839)
    ·
      refine ⟨61127212341854772711760259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40751474894569848474506839 61127212341854772711760259)
      ·
        refine ⟨91690818512782159067640389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61127212341854772711760259 91690818512782159067640389)
        ·
          refine ⟨17192028471146654825182573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91690818512782159067640389 17192028471146654825182573)
          ·
            refine ⟨6447010676679995559443465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17192028471146654825182573 6447010676679995559443465)
            ·
              refine ⟨4835258007509996669582599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447010676679995559443465 4835258007509996669582599)
              ·
                refine ⟨7252887011264995004373899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835258007509996669582599 7252887011264995004373899)
                ·
                  refine ⟨10879330516897492506560849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7252887011264995004373899 10879330516897492506560849)
                  ·
                    refine ⟨8159497887673119379920637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10879330516897492506560849 8159497887673119379920637)
                    ·
                      refine ⟨3059811707877419767470239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8159497887673119379920637 3059811707877419767470239)
                      ·
                        rfl

theorem cell23_5958962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_5958962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958962 prefixEnd_5958962 := by exact prefixLift 5958962
  have htrace : WordTrace (prefixWord ++ tailWord_5958962) baseStart_5958962 baseEnd_5958962 := by
    simpa [prefixWord, tailWord_5958962, baseEnd_5958962] using wordTrace_append hprefix tailTrace_5958962
  have hstable : (prefixWord ++ tailWord_5958962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958962).length < 2 ^ (prefixWord ++ tailWord_5958962).sum := by decide
  have hdescent : baseEnd_5958962 < baseStart_5958962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958975 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 3]
def baseStart_5958975 : Nat := 118140960795 + 5958975 * 2 ^ 59
def prefixEnd_5958975 : Nat := 4983230072969 + 3 ^ 40 * 5958975 * 2
def baseEnd_5958975 : Nat := 3059818383125928216607679

theorem tailTrace_5958975 : CollatzResearch.WordTrace tailWord_5958975 prefixEnd_5958975 3059818383125928216607679 := by
  unfold tailWord_5958975
  simp only [CollatzResearch.WordTrace]
  refine ⟨217341673586658761750926379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144894449057772507833950919 217341673586658761750926379)
  ·
    refine ⟨326012510379988142626389569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217341673586658761750926379 326012510379988142626389569)
    ·
      refine ⟨244509382784991106969792177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326012510379988142626389569 244509382784991106969792177)
      ·
        refine ⟨183382037088743330227344133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244509382784991106969792177 183382037088743330227344133)
        ·
          refine ⟨34384131954139374417627025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183382037088743330227344133 34384131954139374417627025)
          ·
            refine ⟨25788098965604530813220269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34384131954139374417627025 25788098965604530813220269)
            ·
              refine ⟨9670537112101699054957601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25788098965604530813220269 9670537112101699054957601)
              ·
                refine ⟨7252902834076274291218201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9670537112101699054957601 7252902834076274291218201)
                ·
                  refine ⟨5439677125557205718413651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7252902834076274291218201 5439677125557205718413651)
                  ·
                    refine ⟨8159515688335808577620477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5439677125557205718413651 8159515688335808577620477)
                    ·
                      refine ⟨3059818383125928216607679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8159515688335808577620477 3059818383125928216607679)
                      ·
                        rfl

theorem cell23_5958975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_5958975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958975 prefixEnd_5958975 := by exact prefixLift 5958975
  have htrace : WordTrace (prefixWord ++ tailWord_5958975) baseStart_5958975 baseEnd_5958975 := by
    simpa [prefixWord, tailWord_5958975, baseEnd_5958975] using wordTrace_append hprefix tailTrace_5958975
  have hstable : (prefixWord ++ tailWord_5958975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958975).length < 2 ^ (prefixWord ++ tailWord_5958975).sum := by decide
  have hdescent : baseEnd_5958975 < baseStart_5958975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5958989 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5958989 : Nat := 118140960795 + 5958989 * 2 ^ 59
def prefixEnd_5958989 : Nat := 4983230072969 + 3 ^ 40 * 5958989 * 2
def baseEnd_5958989 : Nat := 3059825571855091161832615

theorem tailTrace_5958989 : CollatzResearch.WordTrace tailWord_5958989 prefixEnd_5958989 3059825571855091161832615 := by
  unfold tailWord_5958989
  simp only [CollatzResearch.WordTrace]
  refine ⟨217342184208608042141936021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144894789472405361427957347 217342184208608042141936021)
  ·
    refine ⟨10187914884778501975403251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217342184208608042141936021 10187914884778501975403251)
    ·
      refine ⟨15281872327167752963104877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10187914884778501975403251 15281872327167752963104877)
      ·
        refine ⟨5730702122687907361164329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15281872327167752963104877 5730702122687907361164329)
        ·
          refine ⟨4298026592015930520873247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5730702122687907361164329 4298026592015930520873247)
          ·
            refine ⟨6447039888023895781309871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298026592015930520873247 6447039888023895781309871)
            ·
              refine ⟨9670559832035843671964807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447039888023895781309871 9670559832035843671964807)
              ·
                refine ⟨14505839748053765507947211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9670559832035843671964807 14505839748053765507947211)
                ·
                  refine ⟨21758759622080648261920817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14505839748053765507947211 21758759622080648261920817)
                  ·
                    refine ⟨16319069716560486196440613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21758759622080648261920817 16319069716560486196440613)
                    ·
                      refine ⟨3059825571855091161832615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16319069716560486196440613 3059825571855091161832615)
                      ·
                        rfl

theorem cell23_5958989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5958989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5958989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5958989 prefixEnd_5958989 := by exact prefixLift 5958989
  have htrace : WordTrace (prefixWord ++ tailWord_5958989) baseStart_5958989 baseEnd_5958989 := by
    simpa [prefixWord, tailWord_5958989, baseEnd_5958989] using wordTrace_append hprefix tailTrace_5958989
  have hstable : (prefixWord ++ tailWord_5958989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5958989).length < 2 ^ (prefixWord ++ tailWord_5958989).sum := by decide
  have hdescent : baseEnd_5958989 < baseStart_5958989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5958989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959001 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 3]
def baseStart_5959001 : Nat := 118140960795 + 5959001 * 2 ^ 59
def prefixEnd_5959001 : Nat := 4983230072969 + 3 ^ 40 * 5959001 * 2
def baseEnd_5959001 : Nat := 3059831733622945114882559

theorem tailTrace_5959001 : CollatzResearch.WordTrace tailWord_5959001 prefixEnd_5959001 3059831733622945114882559 := by
  unfold tailWord_5959001
  simp only [CollatzResearch.WordTrace]
  refine ⟨217342621884564568191372857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144895081256376378794248571 217342621884564568191372857)
  ·
    refine ⟨163006966413423426143529643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217342621884564568191372857 163006966413423426143529643)
    ·
      refine ⟨244510449620135139215294465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163006966413423426143529643 244510449620135139215294465)
      ·
        refine ⟨183382837215101354411470849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244510449620135139215294465 183382837215101354411470849)
        ·
          refine ⟨137537127911326015808603137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183382837215101354411470849 137537127911326015808603137)
          ·
            refine ⟨103152845933494511856452353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137537127911326015808603137 103152845933494511856452353)
            ·
              refine ⟨77364634450120883892339265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103152845933494511856452353 77364634450120883892339265)
              ·
                refine ⟨58023475837590662919254449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77364634450120883892339265 58023475837590662919254449)
                ·
                  refine ⟨43517606878192997189440837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58023475837590662919254449 43517606878192997189440837)
                  ·
                    refine ⟨8159551289661186973020157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43517606878192997189440837 8159551289661186973020157)
                    ·
                      refine ⟨3059831733622945114882559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8159551289661186973020157 3059831733622945114882559)
                      ·
                        rfl

theorem cell23_5959001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_5959001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959001 prefixEnd_5959001 := by exact prefixLift 5959001
  have htrace : WordTrace (prefixWord ++ tailWord_5959001) baseStart_5959001 baseEnd_5959001 := by
    simpa [prefixWord, tailWord_5959001, baseEnd_5959001] using wordTrace_append hprefix tailTrace_5959001
  have hstable : (prefixWord ++ tailWord_5959001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959001).length < 2 ^ (prefixWord ++ tailWord_5959001).sum := by decide
  have hdescent : baseEnd_5959001 < baseStart_5959001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959051 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 4, 5]
def baseStart_5959051 : Nat := 118140960795 + 5959051 * 2 ^ 59
def prefixEnd_5959051 : Nat := 4983230072969 + 3 ^ 40 * 5959051 * 2
def baseEnd_5959051 : Nat := 1019952469218556639752443

theorem tailTrace_5959051 : CollatzResearch.WordTrace tailWord_5959051 prefixEnd_5959051 1019952469218556639752443 := by
  unfold tailWord_5959051
  simp only [CollatzResearch.WordTrace]
  refine ⟨217344445534383426730693007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144896297022922284487128671 217344445534383426730693007)
  ·
    refine ⟨326016668301575140096039511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217344445534383426730693007 326016668301575140096039511)
    ·
      refine ⟨489025002452362710144059267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326016668301575140096039511 489025002452362710144059267)
      ·
        refine ⟨733537503678544065216088901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489025002452362710144059267 733537503678544065216088901)
        ·
          refine ⟨137538281939727012228016669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 733537503678544065216088901 137538281939727012228016669)
          ·
            refine ⟨51576855727397629585506251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137538281939727012228016669 51576855727397629585506251)
            ·
              refine ⟨77365283591096444378259377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51576855727397629585506251 77365283591096444378259377)
              ·
                refine ⟨58023962693322333283694533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77365283591096444378259377 58023962693322333283694533)
                ·
                  refine ⟨10879493004997937490692725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58023962693322333283694533 10879493004997937490692725)
                  ·
                    refine ⟨1019952469218556639752443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10879493004997937490692725 1019952469218556639752443)
                    ·
                      rfl

theorem cell23_5959051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 5].length) (baseStart_5959051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959051 prefixEnd_5959051 := by exact prefixLift 5959051
  have htrace : WordTrace (prefixWord ++ tailWord_5959051) baseStart_5959051 baseEnd_5959051 := by
    simpa [prefixWord, tailWord_5959051, baseEnd_5959051] using wordTrace_append hprefix tailTrace_5959051
  have hstable : (prefixWord ++ tailWord_5959051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959051).length < 2 ^ (prefixWord ++ tailWord_5959051).sum := by decide
  have hdescent : baseEnd_5959051 < baseStart_5959051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959085 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_5959085 : Nat := 118140960795 + 5959085 * 2 ^ 59
def prefixEnd_5959085 : Nat := 4983230072969 + 3 ^ 40 * 5959085 * 2
def baseEnd_5959085 : Nat := 1019958288665974262077391

theorem tailTrace_5959085 : CollatzResearch.WordTrace tailWord_5959085 prefixEnd_5959085 1019958288665974262077391 := by
  unfold tailWord_5959085
  simp only [CollatzResearch.WordTrace]
  refine ⟨217345685616260250537430709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144897123744173500358287139 217345685616260250537430709)
  ·
    refine ⟨20376158026524398487884129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217345685616260250537430709 20376158026524398487884129)
    ·
      refine ⟨15282118519893298865913097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20376158026524398487884129 15282118519893298865913097)
      ·
        refine ⟨11461588889919974149434823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15282118519893298865913097 11461588889919974149434823)
        ·
          refine ⟨17192383334879961224152235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11461588889919974149434823 17192383334879961224152235)
          ·
            refine ⟨25788575002319941836228353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17192383334879961224152235 25788575002319941836228353)
            ·
              refine ⟨19341431251739956377171265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25788575002319941836228353 19341431251739956377171265)
              ·
                refine ⟨14506073438804967282878449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19341431251739956377171265 14506073438804967282878449)
                ·
                  refine ⟨10879555079103725462158837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14506073438804967282878449 10879555079103725462158837)
                  ·
                    refine ⟨1019958288665974262077391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10879555079103725462158837 1019958288665974262077391)
                    ·
                      rfl

theorem cell23_5959085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_5959085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959085 prefixEnd_5959085 := by exact prefixLift 5959085
  have htrace : WordTrace (prefixWord ++ tailWord_5959085) baseStart_5959085 baseEnd_5959085 := by
    simpa [prefixWord, tailWord_5959085, baseEnd_5959085] using wordTrace_append hprefix tailTrace_5959085
  have hstable : (prefixWord ++ tailWord_5959085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959085).length < 2 ^ (prefixWord ++ tailWord_5959085).sum := by decide
  have hdescent : baseEnd_5959085 < baseStart_5959085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959165 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_5959165 : Nat := 118140960795 + 5959165 * 2 ^ 59
def prefixEnd_5959165 : Nat := 4983230072969 + 3 ^ 40 * 5959165 * 2
def baseEnd_5959165 : Nat := 3059915944450282473231805

theorem tailTrace_5959165 : CollatzResearch.WordTrace tailWord_5959165 prefixEnd_5959165 3059915944450282473231805 := by
  unfold tailWord_5959165
  simp only [CollatzResearch.WordTrace]
  refine ⟨217348603455970424200342949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144899068970646949466895299 217348603455970424200342949)
  ·
    refine ⟨40752863147994454537564303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217348603455970424200342949 40752863147994454537564303)
    ·
      refine ⟨61129294721991681806346455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40752863147994454537564303 61129294721991681806346455)
      ·
        refine ⟨91693942082987522709519683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61129294721991681806346455 91693942082987522709519683)
        ·
          refine ⟨137540913124481284064279525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91693942082987522709519683 137540913124481284064279525)
          ·
            refine ⟨25788921210840240762052411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137540913124481284064279525 25788921210840240762052411)
            ·
              refine ⟨38683381816260361143078617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25788921210840240762052411 38683381816260361143078617)
              ·
                refine ⟨29012536362195270857308963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38683381816260361143078617 29012536362195270857308963)
                ·
                  refine ⟨43518804543292906285963445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29012536362195270857308963 43518804543292906285963445)
                  ·
                    refine ⟨4079887925933709964309073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43518804543292906285963445 4079887925933709964309073)
                    ·
                      refine ⟨3059915944450282473231805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079887925933709964309073 3059915944450282473231805)
                      ·
                        rfl

theorem cell23_5959165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_5959165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959165 prefixEnd_5959165 := by exact prefixLift 5959165
  have htrace : WordTrace (prefixWord ++ tailWord_5959165) baseStart_5959165 baseEnd_5959165 := by
    simpa [prefixWord, tailWord_5959165, baseEnd_5959165] using wordTrace_append hprefix tailTrace_5959165
  have hstable : (prefixWord ++ tailWord_5959165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959165).length < 2 ^ (prefixWord ++ tailWord_5959165).sum := by decide
  have hdescent : baseEnd_5959165 < baseStart_5959165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959175 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 1, 5]
def baseStart_5959175 : Nat := 118140960795 + 5959175 * 2 ^ 59
def prefixEnd_5959175 : Nat := 4983230072969 + 3 ^ 40 * 5959175 * 2
def baseEnd_5959175 : Nat := 1019973693085609144702253

theorem tailTrace_5959175 : CollatzResearch.WordTrace tailWord_5959175 prefixEnd_5959175 1019973693085609144702253 := by
  unfold tailWord_5959175
  simp only [CollatzResearch.WordTrace]
  refine ⟨217348968185934195908206979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144899312123956130605471319 217348968185934195908206979)
  ·
    refine ⟨326023452278901293862310469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217348968185934195908206979 326023452278901293862310469)
    ·
      refine ⟨61129397302293992599183213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326023452278901293862310469 61129397302293992599183213)
      ·
        refine ⟨22923523988360247224693705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61129397302293992599183213 22923523988360247224693705)
        ·
          refine ⟨17192642991270185418520279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22923523988360247224693705 17192642991270185418520279)
          ·
            refine ⟨25788964486905278127780419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17192642991270185418520279 25788964486905278127780419)
            ·
              refine ⟨38683446730357917191670629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25788964486905278127780419 38683446730357917191670629)
              ·
                refine ⟨7253146261942109473438243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38683446730357917191670629 7253146261942109473438243)
                ·
                  refine ⟨10879719392913164210157365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7253146261942109473438243 10879719392913164210157365)
                  ·
                    refine ⟨1019973693085609144702253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10879719392913164210157365 1019973693085609144702253)
                    ·
                      rfl

theorem cell23_5959175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_5959175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959175 prefixEnd_5959175 := by exact prefixLift 5959175
  have htrace : WordTrace (prefixWord ++ tailWord_5959175) baseStart_5959175 baseEnd_5959175 := by
    simpa [prefixWord, tailWord_5959175, baseEnd_5959175] using wordTrace_append hprefix tailTrace_5959175
  have hstable : (prefixWord ++ tailWord_5959175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959175).length < 2 ^ (prefixWord ++ tailWord_5959175).sum := by decide
  have hdescent : baseEnd_5959175 < baseStart_5959175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959189 : List Nat := [1, 3, 2, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_5959189 : Nat := 118140960795 + 5959189 * 2 ^ 59
def prefixEnd_5959189 : Nat := 4983230072969 + 3 ^ 40 * 5959189 * 2
def baseEnd_5959189 : Nat := 3059928267985990379331695

theorem tailTrace_5959189 : CollatzResearch.WordTrace tailWord_5959189 prefixEnd_5959189 3059928267985990379331695 := by
  unfold tailWord_5959189
  simp only [CollatzResearch.WordTrace]
  refine ⟨217349478807883476299216621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144899652538588984199477747 217349478807883476299216621)
  ·
    refine ⟨81506054552956303612206233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217349478807883476299216621 81506054552956303612206233)
    ·
      refine ⟨61129540914717227709154675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81506054552956303612206233 61129540914717227709154675)
      ·
        refine ⟨91694311372075841563732013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61129540914717227709154675 91694311372075841563732013)
        ·
          refine ⟨34385366764528440586399505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91694311372075841563732013 34385366764528440586399505)
          ·
            refine ⟨25789025073396330439799629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34385366764528440586399505 25789025073396330439799629)
            ·
              refine ⟨9670884402523623914924861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25789025073396330439799629 9670884402523623914924861)
              ·
                refine ⟨3626581650946358968096823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9670884402523623914924861 3626581650946358968096823)
                ·
                  refine ⟨5439872476419538452145235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626581650946358968096823 5439872476419538452145235)
                  ·
                    refine ⟨8159808714629307678217853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5439872476419538452145235 8159808714629307678217853)
                    ·
                      refine ⟨3059928267985990379331695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8159808714629307678217853 3059928267985990379331695)
                      ·
                        rfl

theorem cell23_5959189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_5959189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959189 prefixEnd_5959189 := by exact prefixLift 5959189
  have htrace : WordTrace (prefixWord ++ tailWord_5959189) baseStart_5959189 baseEnd_5959189 := by
    simpa [prefixWord, tailWord_5959189, baseEnd_5959189] using wordTrace_append hprefix tailTrace_5959189
  have hstable : (prefixWord ++ tailWord_5959189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959189).length < 2 ^ (prefixWord ++ tailWord_5959189).sum := by decide
  have hdescent : baseEnd_5959189 < baseStart_5959189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959205 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_5959205 : Nat := 118140960795 + 5959205 * 2 ^ 59
def prefixEnd_5959205 : Nat := 4983230072969 + 3 ^ 40 * 5959205 * 2
def baseEnd_5959205 : Nat := 1019978827892154105577207

theorem tailTrace_5959205 : CollatzResearch.WordTrace tailWord_5959205 prefixEnd_5959205 1019978827892154105577207 := by
  unfold tailWord_5959205
  simp only [CollatzResearch.WordTrace]
  refine ⟨217350062375825511031799069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144900041583883674021199379 217350062375825511031799069)
  ·
    refine ⟨81506273390934566636924651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217350062375825511031799069 81506273390934566636924651)
    ·
      refine ⟨122259410086401849955386977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81506273390934566636924651 122259410086401849955386977)
      ·
        refine ⟨91694557564801387466540233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122259410086401849955386977 91694557564801387466540233)
        ·
          refine ⟨68770918173601040599905175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91694557564801387466540233 68770918173601040599905175)
          ·
            refine ⟨103156377260401560899857763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68770918173601040599905175 103156377260401560899857763)
            ·
              refine ⟨154734565890602341349786645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103156377260401560899857763 154734565890602341349786645)
              ·
                refine ⟨7253182776121984750771249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154734565890602341349786645 7253182776121984750771249)
                ·
                  refine ⟨5439887082091488563078437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7253182776121984750771249 5439887082091488563078437)
                  ·
                    refine ⟨1019978827892154105577207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5439887082091488563078437 1019978827892154105577207)
                    ·
                      rfl

theorem cell23_5959205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_5959205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959205 prefixEnd_5959205 := by exact prefixLift 5959205
  have htrace : WordTrace (prefixWord ++ tailWord_5959205) baseStart_5959205 baseEnd_5959205 := by
    simpa [prefixWord, tailWord_5959205, baseEnd_5959205] using wordTrace_append hprefix tailTrace_5959205
  have hstable : (prefixWord ++ tailWord_5959205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959205).length < 2 ^ (prefixWord ++ tailWord_5959205).sum := by decide
  have hdescent : baseEnd_5959205 < baseStart_5959205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959229 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_5959229 : Nat := 118140960795 + 5959229 * 2 ^ 59
def prefixEnd_5959229 : Nat := 4983230072969 + 3 ^ 40 * 5959229 * 2
def baseEnd_5959229 : Nat := 3059948807212170222831511

theorem tailTrace_5959229 : CollatzResearch.WordTrace tailWord_5959229 prefixEnd_5959229 3059948807212170222831511 := by
  unfold tailWord_5959229
  simp only [CollatzResearch.WordTrace]
  refine ⟨217350937727738563130672741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144900625151825708753781827 217350937727738563130672741)
  ·
    refine ⟨40753300823950980587001139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217350937727738563130672741 40753300823950980587001139)
    ·
      refine ⟨61129951235926470880501709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40753300823950980587001139 61129951235926470880501709)
      ·
        refine ⟨22923731713472426580188141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61129951235926470880501709 22923731713472426580188141)
        ·
          refine ⟨8596399392552159967570553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22923731713472426580188141 8596399392552159967570553)
          ·
            refine ⟨6447299544414119975677915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8596399392552159967570553 6447299544414119975677915)
            ·
              refine ⟨9670949316621179963516873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447299544414119975677915 9670949316621179963516873)
              ·
                refine ⟨7253211987465884972637655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9670949316621179963516873 7253211987465884972637655)
                ·
                  refine ⟨10879817981198827458956483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7253211987465884972637655 10879817981198827458956483)
                  ·
                    refine ⟨16319726971798241188434725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10879817981198827458956483 16319726971798241188434725)
                    ·
                      refine ⟨3059948807212170222831511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16319726971798241188434725 3059948807212170222831511)
                      ·
                        rfl

theorem cell23_5959229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_5959229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959229 prefixEnd_5959229 := by exact prefixLift 5959229
  have htrace : WordTrace (prefixWord ++ tailWord_5959229) baseStart_5959229 baseEnd_5959229 := by
    simpa [prefixWord, tailWord_5959229, baseEnd_5959229] using wordTrace_append hprefix tailTrace_5959229
  have hstable : (prefixWord ++ tailWord_5959229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959229).length < 2 ^ (prefixWord ++ tailWord_5959229).sum := by decide
  have hdescent : baseEnd_5959229 < baseStart_5959229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959258 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_5959258 : Nat := 118140960795 + 5959258 * 2 ^ 59
def prefixEnd_5959258 : Nat := 4983230072969 + 3 ^ 40 * 5959258 * 2
def baseEnd_5959258 : Nat := 3059963698151150609368877

theorem tailTrace_5959258 : CollatzResearch.WordTrace tailWord_5959258 prefixEnd_5959258 3059963698151150609368877 := by
  unfold tailWord_5959258
  simp only [CollatzResearch.WordTrace]
  refine ⟨54337998861158375270869607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144901330296422334055652285 54337998861158375270869607)
  ·
    refine ⟨81506998291737562906304411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54337998861158375270869607 81506998291737562906304411)
    ·
      refine ⟨122260497437606344359456617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81506998291737562906304411 122260497437606344359456617)
      ·
        refine ⟨91695373078204758269592463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122260497437606344359456617 91695373078204758269592463)
        ·
          refine ⟨137543059617307137404388695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91695373078204758269592463 137543059617307137404388695)
          ·
            refine ⟨206314589425960706106583043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137543059617307137404388695 206314589425960706106583043)
            ·
              refine ⟨309471884138941059159874565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206314589425960706106583043 309471884138941059159874565)
              ·
                refine ⟨58025978276051448592476481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 309471884138941059159874565 58025978276051448592476481)
                ·
                  refine ⟨43519483707038586444357361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58025978276051448592476481 43519483707038586444357361)
                  ·
                    refine ⟨32639612780278939833268021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43519483707038586444357361 32639612780278939833268021)
                    ·
                      refine ⟨3059963698151150609368877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32639612780278939833268021 3059963698151150609368877)
                      ·
                        rfl

theorem cell23_5959258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_5959258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959258 prefixEnd_5959258 := by exact prefixLift 5959258
  have htrace : WordTrace (prefixWord ++ tailWord_5959258) baseStart_5959258 baseEnd_5959258 := by
    simpa [prefixWord, tailWord_5959258, baseEnd_5959258] using wordTrace_append hprefix tailTrace_5959258
  have hstable : (prefixWord ++ tailWord_5959258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959258).length < 2 ^ (prefixWord ++ tailWord_5959258).sum := by decide
  have hdescent : baseEnd_5959258 < baseStart_5959258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959306 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_5959306 : Nat := 118140960795 + 5959306 * 2 ^ 59
def prefixEnd_5959306 : Nat := 4983230072969 + 3 ^ 40 * 5959306 * 2
def baseEnd_5959306 : Nat := 3059988345222566421568657

theorem tailTrace_5959306 : CollatzResearch.WordTrace tailWord_5959306 prefixEnd_5959306 3059988345222566421568657 := by
  unfold tailWord_5959306
  simp only [CollatzResearch.WordTrace]
  refine ⟨54338436537114901320306443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144902497432306403520817181 54338436537114901320306443)
  ·
    refine ⟨81507654805672351980459665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54338436537114901320306443 81507654805672351980459665)
    ·
      refine ⟨61130741104254263985344749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81507654805672351980459665 61130741104254263985344749)
      ·
        refine ⟨22924027914095348994504281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61130741104254263985344749 22924027914095348994504281)
        ·
          refine ⟨17193020935571511745878211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22924027914095348994504281 17193020935571511745878211)
          ·
            refine ⟨25789531403357267618817317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17193020935571511745878211 25789531403357267618817317)
            ·
              refine ⟨4835537138129487678528247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25789531403357267618817317 4835537138129487678528247)
              ·
                refine ⟨7253305707194231517792371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835537138129487678528247 7253305707194231517792371)
                ·
                  refine ⟨10879958560791347276688557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7253305707194231517792371 10879958560791347276688557)
                  ·
                    refine ⟨4079984460296755228758209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10879958560791347276688557 4079984460296755228758209)
                    ·
                      refine ⟨3059988345222566421568657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079984460296755228758209 3059988345222566421568657)
                      ·
                        rfl

theorem cell23_5959306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_5959306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959306 prefixEnd_5959306 := by exact prefixLift 5959306
  have htrace : WordTrace (prefixWord ++ tailWord_5959306) baseStart_5959306 baseEnd_5959306 := by
    simpa [prefixWord, tailWord_5959306, baseEnd_5959306] using wordTrace_append hprefix tailTrace_5959306
  have hstable : (prefixWord ++ tailWord_5959306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959306).length < 2 ^ (prefixWord ++ tailWord_5959306).sum := by decide
  have hdescent : baseEnd_5959306 < baseStart_5959306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959308 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 9]
def baseStart_5959308 : Nat := 118140960795 + 5959308 * 2 ^ 59
def prefixEnd_5959308 : Nat := 4983230072969 + 3 ^ 40 * 5959308 * 2
def baseEnd_5959308 : Nat := 339998819131541712638183

theorem tailTrace_5959308 : CollatzResearch.WordTrace tailWord_5959308 prefixEnd_5959308 339998819131541712638183 := by
  unfold tailWord_5959308
  simp only [CollatzResearch.WordTrace]
  refine ⟨108676909547226179811399289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144902546062968239748532385 108676909547226179811399289)
  ·
    refine ⟨81507682160419634858549467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108676909547226179811399289 81507682160419634858549467)
    ·
      refine ⟨122261523240629452287824201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81507682160419634858549467 122261523240629452287824201)
      ·
        refine ⟨91696142430472089215868151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122261523240629452287824201 91696142430472089215868151)
        ·
          refine ⟨137544213645708133823802227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91696142430472089215868151 137544213645708133823802227)
          ·
            refine ⟨206316320468562200735703341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137544213645708133823802227 206316320468562200735703341)
            ·
              refine ⟨77368620175710825275888753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206316320468562200735703341 77368620175710825275888753)
              ·
                refine ⟨58026465131783118956916565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77368620175710825275888753 58026465131783118956916565)
                ·
                  refine ⟨339998819131541712638183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58026465131783118956916565 339998819131541712638183)
                  ·
                    rfl

theorem cell23_5959308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_5959308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959308 prefixEnd_5959308 := by exact prefixLift 5959308
  have htrace : WordTrace (prefixWord ++ tailWord_5959308) baseStart_5959308 baseEnd_5959308 := by
    simpa [prefixWord, tailWord_5959308, baseEnd_5959308] using wordTrace_append hprefix tailTrace_5959308
  have hstable : (prefixWord ++ tailWord_5959308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959308).length < 2 ^ (prefixWord ++ tailWord_5959308).sum := by decide
  have hdescent : baseEnd_5959308 < baseStart_5959308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959319 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 4, 2, 2]
def baseStart_5959319 : Nat := 118140960795 + 5959319 * 2 ^ 59
def prefixEnd_5959319 : Nat := 4983230072969 + 3 ^ 40 * 5959319 * 2
def baseEnd_5959319 : Nat := 3059995020471074870706097

theorem tailTrace_5959319 : CollatzResearch.WordTrace tailWord_5959319 prefixEnd_5959319 3059995020471074870706097 := by
  unfold tailWord_5959319
  simp only [CollatzResearch.WordTrace]
  refine ⟨217354220297412508501449011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144902813531608339000966007 217354220297412508501449011)
  ·
    refine ⟨326031330446118762752173517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217354220297412508501449011 326031330446118762752173517)
    ·
      refine ⟨122261748917294536032065069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326031330446118762752173517 122261748917294536032065069)
      ·
        refine ⟨45848155843985451012024401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122261748917294536032065069 45848155843985451012024401)
        ·
          refine ⟨34386116882989088259018301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45848155843985451012024401 34386116882989088259018301)
          ·
            refine ⟨12894793831120908097131863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34386116882989088259018301 12894793831120908097131863)
            ·
              refine ⟨19342190746681362145697795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12894793831120908097131863 19342190746681362145697795)
              ·
                refine ⟨29013286120022043218546693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19342190746681362145697795 29013286120022043218546693)
                ·
                  refine ⟨5439991147504133103477505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29013286120022043218546693 5439991147504133103477505)
                  ·
                    refine ⟨4079993360628099827608129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5439991147504133103477505 4079993360628099827608129)
                    ·
                      refine ⟨3059995020471074870706097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4079993360628099827608129 3059995020471074870706097)
                      ·
                        rfl

theorem cell23_5959319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_5959319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959319 prefixEnd_5959319 := by exact prefixLift 5959319
  have htrace : WordTrace (prefixWord ++ tailWord_5959319) baseStart_5959319 baseEnd_5959319 := by
    simpa [prefixWord, tailWord_5959319, baseEnd_5959319] using wordTrace_append hprefix tailTrace_5959319
  have hstable : (prefixWord ++ tailWord_5959319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959319).length < 2 ^ (prefixWord ++ tailWord_5959319).sum := by decide
  have hdescent : baseEnd_5959319 < baseStart_5959319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959392 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 2, 4, 2]
def baseStart_5959392 : Nat := 118140960795 + 5959392 * 2 ^ 59
def prefixEnd_5959392 : Nat := 4983230072969 + 3 ^ 40 * 5959392 * 2
def baseEnd_5959392 : Nat := 3060032504558853085093261

theorem tailTrace_5959392 : CollatzResearch.WordTrace tailWord_5959392 prefixEnd_5959392 3060032504558853085093261 := by
  unfold tailWord_5959392
  simp only [CollatzResearch.WordTrace]
  refine ⟨108678441413074020984428215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144904588550765361312570953 108678441413074020984428215)
  ·
    refine ⟨163017662119611031476642323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108678441413074020984428215 163017662119611031476642323)
    ·
      refine ⟨244526493179416547214963485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163017662119611031476642323 244526493179416547214963485)
      ·
        refine ⟨91697434942281205205611307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244526493179416547214963485 91697434942281205205611307)
        ·
          refine ⟨137546152413421807808416961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91697434942281205205611307 137546152413421807808416961)
          ·
            refine ⟨103159614310066355856312721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137546152413421807808416961 103159614310066355856312721)
            ·
              refine ⟨77369710732549766892234541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103159614310066355856312721 77369710732549766892234541)
              ·
                refine ⟨29013641524706162584587953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77369710732549766892234541 29013641524706162584587953)
                ·
                  refine ⟨21760231143529621938440965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29013641524706162584587953 21760231143529621938440965)
                  ·
                    refine ⟨4080043339411804113457681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21760231143529621938440965 4080043339411804113457681)
                    ·
                      refine ⟨3060032504558853085093261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080043339411804113457681 3060032504558853085093261)
                      ·
                        rfl

theorem cell23_5959392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_5959392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959392 prefixEnd_5959392 := by exact prefixLift 5959392
  have htrace : WordTrace (prefixWord ++ tailWord_5959392) baseStart_5959392 baseEnd_5959392 := by
    simpa [prefixWord, tailWord_5959392, baseEnd_5959392] using wordTrace_append hprefix tailTrace_5959392
  have hstable : (prefixWord ++ tailWord_5959392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959392).length < 2 ^ (prefixWord ++ tailWord_5959392).sum := by decide
  have hdescent : baseEnd_5959392 < baseStart_5959392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959402 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_5959402 : Nat := 118140960795 + 5959402 * 2 ^ 59
def prefixEnd_5959402 : Nat := 4983230072969 + 3 ^ 40 * 5959402 * 2
def baseEnd_5959402 : Nat := 1020012546455132681989405

theorem tailTrace_5959402 : CollatzResearch.WordTrace tailWord_5959402 prefixEnd_5959402 1020012546455132681989405 := by
  unfold tailWord_5959402
  simp only [CollatzResearch.WordTrace]
  refine ⟨54339311889027953419180115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144904831704074542451146973 54339311889027953419180115)
  ·
    refine ⟨81508967833541930128770173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54339311889027953419180115 81508967833541930128770173)
    ·
      refine ⟨30565862937578223798288815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81508967833541930128770173 30565862937578223798288815)
      ·
        refine ⟨45848794406367335697433223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30565862937578223798288815 45848794406367335697433223)
        ·
          refine ⟨68773191609551003546149835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45848794406367335697433223 68773191609551003546149835)
          ·
            refine ⟨103159787414326505319224753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68773191609551003546149835 103159787414326505319224753)
            ·
              refine ⟨77369840560744878989418565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103159787414326505319224753 77369840560744878989418565)
              ·
                refine ⟨14506845105139664810515981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77369840560744878989418565 14506845105139664810515981)
                ·
                  refine ⟨5440066914427374303943493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14506845105139664810515981 5440066914427374303943493)
                  ·
                    refine ⟨1020012546455132681989405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440066914427374303943493 1020012546455132681989405)
                    ·
                      rfl

theorem cell23_5959402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_5959402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959402 prefixEnd_5959402 := by exact prefixLift 5959402
  have htrace : WordTrace (prefixWord ++ tailWord_5959402) baseStart_5959402 baseEnd_5959402 := by
    simpa [prefixWord, tailWord_5959402, baseEnd_5959402] using wordTrace_append hprefix tailTrace_5959402
  have hstable : (prefixWord ++ tailWord_5959402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959402).length < 2 ^ (prefixWord ++ tailWord_5959402).sum := by decide
  have hdescent : baseEnd_5959402 < baseStart_5959402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959432 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 6]
def baseStart_5959432 : Nat := 118140960795 + 5959432 * 2 ^ 59
def prefixEnd_5959432 : Nat := 4983230072969 + 3 ^ 40 * 5959432 * 2
def baseEnd_5959432 : Nat := 340005893753892547621453

theorem tailTrace_5959432 : CollatzResearch.WordTrace tailWord_5959432 prefixEnd_5959432 340005893753892547621453 := by
  unfold tailWord_5959432
  simp only [CollatzResearch.WordTrace]
  refine ⟨108679170873001564400156275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144905561164002085866875033 108679170873001564400156275)
  ·
    refine ⟨163018756309502346600234413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108679170873001564400156275 163018756309502346600234413)
    ·
      refine ⟨61132033616063379975087905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163018756309502346600234413 61132033616063379975087905)
      ·
        refine ⟨45849025212047534981315929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61132033616063379975087905 45849025212047534981315929)
        ·
          refine ⟨34386768909035651235986947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45849025212047534981315929 34386768909035651235986947)
          ·
            refine ⟨51580153363553476853980421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34386768909035651235986947 51580153363553476853980421)
            ·
              refine ⟨9671278755666276910121329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51580153363553476853980421 9671278755666276910121329)
              ·
                refine ⟨7253459066749707682590997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9671278755666276910121329 7253459066749707682590997)
                ·
                  refine ⟨340005893753892547621453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7253459066749707682590997 340005893753892547621453)
                  ·
                    rfl

theorem cell23_5959432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 6].length) (baseStart_5959432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959432 prefixEnd_5959432 := by exact prefixLift 5959432
  have htrace : WordTrace (prefixWord ++ tailWord_5959432) baseStart_5959432 baseEnd_5959432 := by
    simpa [prefixWord, tailWord_5959432, baseEnd_5959432] using wordTrace_append hprefix tailTrace_5959432
  have hstable : (prefixWord ++ tailWord_5959432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959432).length < 2 ^ (prefixWord ++ tailWord_5959432).sum := by decide
  have hdescent : baseEnd_5959432 < baseStart_5959432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959436 : List Nat := [2, 2, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_5959436 : Nat := 118140960795 + 5959436 * 2 ^ 59
def prefixEnd_5959436 : Nat := 4983230072969 + 3 ^ 40 * 5959436 * 2
def baseEnd_5959436 : Nat := 1020018365902550304314353

theorem tailTrace_5959436 : CollatzResearch.WordTrace tailWord_5959436 prefixEnd_5959436 1020018365902550304314353 := by
  unfold tailWord_5959436
  simp only [CollatzResearch.WordTrace]
  refine ⟨108679243818994318741729081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144905658425325758322305441 108679243818994318741729081)
  ·
    refine ⟨81509432864245739056296811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108679243818994318741729081 81509432864245739056296811)
    ·
      refine ⟨122264149296368608584445217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81509432864245739056296811 122264149296368608584445217)
      ·
        refine ⟨91698111972276456438333913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122264149296368608584445217 91698111972276456438333913)
        ·
          refine ⟨68773583979207342328750435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91698111972276456438333913 68773583979207342328750435)
          ·
            refine ⟨103160375968811013493125653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68773583979207342328750435 103160375968811013493125653)
            ·
              refine ⟨4835642623538016257490265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103160375968811013493125653 4835642623538016257490265)
              ·
                refine ⟨3626731967653512193117699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4835642623538016257490265 3626731967653512193117699)
                ·
                  refine ⟨5440097951480268289676549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626731967653512193117699 5440097951480268289676549)
                  ·
                    refine ⟨1020018365902550304314353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440097951480268289676549 1020018365902550304314353)
                    ·
                      rfl

theorem cell23_5959436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_5959436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959436 prefixEnd_5959436 := by exact prefixLift 5959436
  have htrace : WordTrace (prefixWord ++ tailWord_5959436) baseStart_5959436 baseEnd_5959436 := by
    simpa [prefixWord, tailWord_5959436, baseEnd_5959436] using wordTrace_append hprefix tailTrace_5959436
  have hstable : (prefixWord ++ tailWord_5959436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959436).length < 2 ^ (prefixWord ++ tailWord_5959436).sum := by decide
  have hdescent : baseEnd_5959436 < baseStart_5959436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959455 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_5959455 : Nat := 118140960795 + 5959455 * 2 ^ 59
def prefixEnd_5959455 : Nat := 4983230072969 + 3 ^ 40 * 5959455 * 2
def baseEnd_5959455 : Nat := 3060064853840086338605471

theorem tailTrace_5959455 : CollatzResearch.WordTrace tailWord_5959455 prefixEnd_5959455 3060064853840086338605471 := by
  unfold tailWord_5959455
  simp only [CollatzResearch.WordTrace]
  refine ⟨217359180624919803728399819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144906120416613202485599879 217359180624919803728399819)
  ·
    refine ⟨326038770937379705592599729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217359180624919803728399819 326038770937379705592599729)
    ·
      refine ⟨244529078203034779194449797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326038770937379705592599729 244529078203034779194449797)
      ·
        refine ⟨45849202163069021098959337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244529078203034779194449797 45849202163069021098959337)
        ·
          refine ⟨34386901622301765824219503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45849202163069021098959337 34386901622301765824219503)
          ·
            refine ⟨51580352433452648736329255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34386901622301765824219503 51580352433452648736329255)
            ·
              refine ⟨77370528650178973104493883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51580352433452648736329255 77370528650178973104493883)
              ·
                refine ⟨116055792975268459656740825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77370528650178973104493883 116055792975268459656740825)
                ·
                  refine ⟨87041844731451344742555619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116055792975268459656740825 87041844731451344742555619)
                  ·
                    refine ⟨130562767097177017113833429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87041844731451344742555619 130562767097177017113833429)
                    ·
                      refine ⟨3060064853840086338605471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130562767097177017113833429 3060064853840086338605471)
                      ·
                        rfl

theorem cell23_5959455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_5959455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959455 prefixEnd_5959455 := by exact prefixLift 5959455
  have htrace : WordTrace (prefixWord ++ tailWord_5959455) baseStart_5959455 baseEnd_5959455 := by
    simpa [prefixWord, tailWord_5959455, baseEnd_5959455] using wordTrace_append hprefix tailTrace_5959455
  have hstable : (prefixWord ++ tailWord_5959455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959455).length < 2 ^ (prefixWord ++ tailWord_5959455).sum := by decide
  have hdescent : baseEnd_5959455 < baseStart_5959455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959509 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_5959509 : Nat := 118140960795 + 5959509 * 2 ^ 59
def prefixEnd_5959509 : Nat := 4983230072969 + 3 ^ 40 * 5959509 * 2
def baseEnd_5959509 : Nat := 1020030860598476375776741

theorem tailTrace_5959509 : CollatzResearch.WordTrace tailWord_5959509 prefixEnd_5959509 1020030860598476375776741 := by
  unfold tailWord_5959509
  simp only [CollatzResearch.WordTrace]
  refine ⟨217361150166724170950865581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144907433444482780633910387 217361150166724170950865581)
  ·
    refine ⟨81510431312521564106574593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217361150166724170950865581 81510431312521564106574593)
    ·
      refine ⟨61132823484391173079930945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81510431312521564106574593 61132823484391173079930945)
      ·
        refine ⟨45849617613293379809948209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61132823484391173079930945 45849617613293379809948209)
        ·
          refine ⟨34387213209970034857461157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45849617613293379809948209 34387213209970034857461157)
          ·
            refine ⟨6447602476869381535773967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34387213209970034857461157 6447602476869381535773967)
            ·
              refine ⟨9671403715304072303660951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447602476869381535773967 9671403715304072303660951)
              ·
                refine ⟨14507105572956108455491427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671403715304072303660951 14507105572956108455491427)
                ·
                  refine ⟨21760658359434162683237141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14507105572956108455491427 21760658359434162683237141)
                  ·
                    refine ⟨1020030860598476375776741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21760658359434162683237141 1020030860598476375776741)
                    ·
                      rfl

theorem cell23_5959509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_5959509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959509 prefixEnd_5959509 := by exact prefixLift 5959509
  have htrace : WordTrace (prefixWord ++ tailWord_5959509) baseStart_5959509 baseEnd_5959509 := by
    simpa [prefixWord, tailWord_5959509, baseEnd_5959509] using wordTrace_append hprefix tailTrace_5959509
  have hstable : (prefixWord ++ tailWord_5959509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959509).length < 2 ^ (prefixWord ++ tailWord_5959509).sum := by decide
  have hdescent : baseEnd_5959509 < baseStart_5959509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959519 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 3]
def baseStart_5959519 : Nat := 118140960795 + 5959519 * 2 ^ 59
def prefixEnd_5959519 : Nat := 4983230072969 + 3 ^ 40 * 5959519 * 2
def baseEnd_5959519 : Nat := 3060097716601974088205177

theorem tailTrace_5959519 : CollatzResearch.WordTrace tailWord_5959519 prefixEnd_5959519 3060097716601974088205177 := by
  unfold tailWord_5959519
  simp only [CollatzResearch.WordTrace]
  refine ⟨217361514896687942658729611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144907676597791961772486407 217361514896687942658729611)
  ·
    refine ⟨326042272345031913988094417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217361514896687942658729611 326042272345031913988094417)
    ·
      refine ⟨244531704258773935491070813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326042272345031913988094417 244531704258773935491070813)
      ·
        refine ⟨91699389097040225809151555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244531704258773935491070813 91699389097040225809151555)
        ·
          refine ⟨137549083645560338713727333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91699389097040225809151555 137549083645560338713727333)
          ·
            refine ⟨25790453183542563508823875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137549083645560338713727333 25790453183542563508823875)
            ·
              refine ⟨38685679775313845263235813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25790453183542563508823875 38685679775313845263235813)
              ·
                refine ⟨7253564957871345986856715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38685679775313845263235813 7253564957871345986856715)
                ·
                  refine ⟨10880347436807018980285073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7253564957871345986856715 10880347436807018980285073)
                  ·
                    refine ⟨8160260577605264235213805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10880347436807018980285073 8160260577605264235213805)
                    ·
                      refine ⟨3060097716601974088205177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8160260577605264235213805 3060097716601974088205177)
                      ·
                        rfl

theorem cell23_5959519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_5959519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959519 prefixEnd_5959519 := by exact prefixLift 5959519
  have htrace : WordTrace (prefixWord ++ tailWord_5959519) baseStart_5959519 baseEnd_5959519 := by
    simpa [prefixWord, tailWord_5959519, baseEnd_5959519] using wordTrace_append hprefix tailTrace_5959519
  have hstable : (prefixWord ++ tailWord_5959519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959519).length < 2 ^ (prefixWord ++ tailWord_5959519).sum := by decide
  have hdescent : baseEnd_5959519 < baseStart_5959519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959535 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 9]
def baseStart_5959535 : Nat := 118140960795 + 5959535 * 2 ^ 59
def prefixEnd_5959535 : Nat := 4983230072969 + 3 ^ 40 * 5959535 * 2
def baseEnd_5959535 : Nat := 1020035310764148675201701

theorem tailTrace_5959535 : CollatzResearch.WordTrace tailWord_5959535 prefixEnd_5959535 1020035310764148675201701 := by
  unfold tailWord_5959535
  simp only [CollatzResearch.WordTrace]
  refine ⟨217362098464629977391312059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144908065643086651594208039 217362098464629977391312059)
  ·
    refine ⟨326043147696944966086968089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217362098464629977391312059 326043147696944966086968089)
    ·
      refine ⟨244532360772708724565226067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326043147696944966086968089 244532360772708724565226067)
      ·
        refine ⟨366798541159063086847839101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244532360772708724565226067 366798541159063086847839101)
        ·
          refine ⟨137549452934648657567939663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 366798541159063086847839101 137549452934648657567939663)
          ·
            refine ⟨206324179401972986351909495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137549452934648657567939663 206324179401972986351909495)
            ·
              refine ⟨309486269102959479527864243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206324179401972986351909495 309486269102959479527864243)
              ·
                refine ⟨464229403654439219291796365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309486269102959479527864243 464229403654439219291796365)
                ·
                  refine ⟨174086026370414707234423637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464229403654439219291796365 174086026370414707234423637)
                  ·
                    refine ⟨1020035310764148675201701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 174086026370414707234423637 1020035310764148675201701)
                    ·
                      rfl

theorem cell23_5959535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_5959535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959535 prefixEnd_5959535 := by exact prefixLift 5959535
  have htrace : WordTrace (prefixWord ++ tailWord_5959535) baseStart_5959535 baseEnd_5959535 := by
    simpa [prefixWord, tailWord_5959535, baseEnd_5959535] using wordTrace_append hprefix tailTrace_5959535
  have hstable : (prefixWord ++ tailWord_5959535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959535).length < 2 ^ (prefixWord ++ tailWord_5959535).sum := by decide
  have hdescent : baseEnd_5959535 < baseStart_5959535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959550 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5959550 : Nat := 118140960795 + 5959550 * 2 ^ 59
def prefixEnd_5959550 : Nat := 4983230072969 + 3 ^ 40 * 5959550 * 2
def baseEnd_5959550 : Nat := 3060113634502263466917535

theorem tailTrace_5959550 : CollatzResearch.WordTrace tailWord_5959550 prefixEnd_5959550 3060113634502263466917535 := by
  unfold tailWord_5959550
  simp only [CollatzResearch.WordTrace]
  refine ⟨27170330694946954369138513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144908430373050423302072069 27170330694946954369138513)
  ·
    refine ⟨20377748021210215776853885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27170330694946954369138513 20377748021210215776853885)
    ·
      refine ⟨7641655507953830916320207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20377748021210215776853885 7641655507953830916320207)
      ·
        refine ⟨11462483261930746374480311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641655507953830916320207 11462483261930746374480311)
        ·
          refine ⟨17193724892896119561720467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11462483261930746374480311 17193724892896119561720467)
          ·
            refine ⟨25790587339344179342580701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17193724892896119561720467 25790587339344179342580701)
            ·
              refine ⟨9671470252254067253467763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25790587339344179342580701 9671470252254067253467763)
              ·
                refine ⟨14507205378381100880201645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671470252254067253467763 14507205378381100880201645)
                ·
                  refine ⟨5440202016892912830075617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14507205378381100880201645 5440202016892912830075617)
                  ·
                    refine ⟨4080151512669684622556713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5440202016892912830075617 4080151512669684622556713)
                    ·
                      refine ⟨3060113634502263466917535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080151512669684622556713 3060113634502263466917535)
                      ·
                        rfl

theorem cell23_5959550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5959550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959550 prefixEnd_5959550 := by exact prefixLift 5959550
  have htrace : WordTrace (prefixWord ++ tailWord_5959550) baseStart_5959550 baseEnd_5959550 := by
    simpa [prefixWord, tailWord_5959550, baseEnd_5959550] using wordTrace_append hprefix tailTrace_5959550
  have hstable : (prefixWord ++ tailWord_5959550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959550).length < 2 ^ (prefixWord ++ tailWord_5959550).sum := by decide
  have hdescent : baseEnd_5959550 < baseStart_5959550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959560 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 2, 4]
def baseStart_5959560 : Nat := 118140960795 + 5959560 * 2 ^ 59
def prefixEnd_5959560 : Nat := 4983230072969 + 3 ^ 40 * 5959560 * 2
def baseEnd_5959560 : Nat := 1020039589769602809264163

theorem tailTrace_5959560 : CollatzResearch.WordTrace tailWord_5959560 prefixEnd_5959560 1020039589769602809264163 := by
  unfold tailWord_5959560
  simp only [CollatzResearch.WordTrace]
  refine ⟨108681505144769703330486067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144908673526359604440648089 108681505144769703330486067)
  ·
    refine ⟨163022257717154554995729101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108681505144769703330486067 163022257717154554995729101)
    ·
      refine ⟨61133346643932958123398413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163022257717154554995729101 61133346643932958123398413)
      ·
        refine ⟨22925004991474859296274405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61133346643932958123398413 22925004991474859296274405)
        ·
          refine ⟨4298438435901536118051451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22925004991474859296274405 4298438435901536118051451)
          ·
            refine ⟨6447657653852304177077177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298438435901536118051451 6447657653852304177077177)
            ·
              refine ⟨4835743240389228132807883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6447657653852304177077177 4835743240389228132807883)
              ·
                refine ⟨7253614860583842199211825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835743240389228132807883 7253614860583842199211825)
                ·
                  refine ⟨5440211145437881649408869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7253614860583842199211825 5440211145437881649408869)
                  ·
                    refine ⟨1020039589769602809264163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440211145437881649408869 1020039589769602809264163)
                    ·
                      rfl

theorem cell23_5959560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_5959560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959560 prefixEnd_5959560 := by exact prefixLift 5959560
  have htrace : WordTrace (prefixWord ++ tailWord_5959560) baseStart_5959560 baseEnd_5959560 := by
    simpa [prefixWord, tailWord_5959560, baseEnd_5959560] using wordTrace_append hprefix tailTrace_5959560
  have hstable : (prefixWord ++ tailWord_5959560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959560).length < 2 ^ (prefixWord ++ tailWord_5959560).sum := by decide
  have hdescent : baseEnd_5959560 < baseStart_5959560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959602 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_5959602 : Nat := 118140960795 + 5959602 * 2 ^ 59
def prefixEnd_5959602 : Nat := 4983230072969 + 3 ^ 40 * 5959602 * 2
def baseEnd_5959602 : Nat := 3060140335496297263467295

theorem tailTrace_5959602 : CollatzResearch.WordTrace tailWord_5959602 prefixEnd_5959602 3060140335496297263467295 := by
  unfold tailWord_5959602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54341135538846811958500265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144909694770258165222667373 54341135538846811958500265)
  ·
    refine ⟨40755851654135108968875199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54341135538846811958500265 40755851654135108968875199)
    ·
      refine ⟨61133777481202663453312799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40755851654135108968875199 61133777481202663453312799)
      ·
        refine ⟨91700666221803995179969199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61133777481202663453312799 91700666221803995179969199)
        ·
          refine ⟨137550999332705992769953799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91700666221803995179969199 137550999332705992769953799)
          ·
            refine ⟨206326498999058989154930699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137550999332705992769953799 206326498999058989154930699)
            ·
              refine ⟨309489748498588483732396049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206326498999058989154930699 309489748498588483732396049)
              ·
                refine ⟨232117311373941362799297037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309489748498588483732396049 232117311373941362799297037)
                ·
                  refine ⟨87043991765228011049736389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232117311373941362799297037 87043991765228011049736389)
                  ·
                    refine ⟨16320748455980252071825573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87043991765228011049736389 16320748455980252071825573)
                    ·
                      refine ⟨3060140335496297263467295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16320748455980252071825573 3060140335496297263467295)
                      ·
                        rfl

theorem cell23_5959602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_5959602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959602 prefixEnd_5959602 := by exact prefixLift 5959602
  have htrace : WordTrace (prefixWord ++ tailWord_5959602) baseStart_5959602 baseEnd_5959602 := by
    simpa [prefixWord, tailWord_5959602, baseEnd_5959602] using wordTrace_append hprefix tailTrace_5959602
  have hstable : (prefixWord ++ tailWord_5959602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959602).length < 2 ^ (prefixWord ++ tailWord_5959602).sum := by decide
  have hdescent : baseEnd_5959602 < baseStart_5959602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959699 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 3]
def baseStart_5959699 : Nat := 118140960795 + 5959699 * 2 ^ 59
def prefixEnd_5959699 : Nat := 4983230072969 + 3 ^ 40 * 5959699 * 2
def baseEnd_5959699 : Nat := 3060190143119783383954349

theorem tailTrace_5959699 : CollatzResearch.WordTrace tailWord_5959699 prefixEnd_5959699 3060190143119783383954349 := by
  unfold tailWord_5959699
  simp only [CollatzResearch.WordTrace]
  refine ⟨217368080036035833400282151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144912053357357222266854767 217368080036035833400282151)
  ·
    refine ⟨326052120054053750100423227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217368080036035833400282151 326052120054053750100423227)
    ·
      refine ⟨489078180081080625150634841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326052120054053750100423227 489078180081080625150634841)
      ·
        refine ⟨366808635060810468862976131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489078180081080625150634841 366808635060810468862976131)
        ·
          refine ⟨550212952591215703294464197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366808635060810468862976131 550212952591215703294464197)
          ·
            refine ⟨103164928610852944367712037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 550212952591215703294464197 103164928610852944367712037)
            ·
              refine ⟨19343424114534927068946007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103164928610852944367712037 19343424114534927068946007)
              ·
                refine ⟨29015136171802390603419011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19343424114534927068946007 29015136171802390603419011)
                ·
                  refine ⟨43522704257703585905128517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29015136171802390603419011 43522704257703585905128517)
                  ·
                    refine ⟨8160507048319422357211597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43522704257703585905128517 8160507048319422357211597)
                    ·
                      refine ⟨3060190143119783383954349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8160507048319422357211597 3060190143119783383954349)
                      ·
                        rfl

theorem cell23_5959699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_5959699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959699 prefixEnd_5959699 := by exact prefixLift 5959699
  have htrace : WordTrace (prefixWord ++ tailWord_5959699) baseStart_5959699 baseEnd_5959699 := by
    simpa [prefixWord, tailWord_5959699, baseEnd_5959699] using wordTrace_append hprefix tailTrace_5959699
  have hstable : (prefixWord ++ tailWord_5959699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959699).length < 2 ^ (prefixWord ++ tailWord_5959699).sum := by decide
  have hdescent : baseEnd_5959699 < baseStart_5959699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959736 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 6]
def baseStart_5959736 : Nat := 118140960795 + 5959736 * 2 ^ 59
def prefixEnd_5959736 : Nat := 4983230072969 + 3 ^ 40 * 5959736 * 2
def baseEnd_5959736 : Nat := 340023237989333304354631

theorem tailTrace_5959736 : CollatzResearch.WordTrace tailWord_5959736 prefixEnd_5959736 340023237989333304354631 := by
  unfold tailWord_5959736
  simp only [CollatzResearch.WordTrace]
  refine ⟨108684714768450894359689531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144912953024601192479586041 108684714768450894359689531)
  ·
    refine ⟨163027072152676341539534297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108684714768450894359689531 163027072152676341539534297)
    ·
      refine ⟨122270304114507256154650723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163027072152676341539534297 122270304114507256154650723)
      ·
        refine ⟨183405456171760884231976085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122270304114507256154650723 183405456171760884231976085)
        ·
          refine ⟨8597130758051291448373879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183405456171760884231976085 8597130758051291448373879)
          ·
            refine ⟨12895696137076937172560819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8597130758051291448373879 12895696137076937172560819)
            ·
              refine ⟨19343544205615405758841229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12895696137076937172560819 19343544205615405758841229)
              ·
                refine ⟨7253829077105777159565461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19343544205615405758841229 7253829077105777159565461)
                ·
                  refine ⟨340023237989333304354631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7253829077105777159565461 340023237989333304354631)
                  ·
                    rfl

theorem cell23_5959736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 6].length) (baseStart_5959736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959736 prefixEnd_5959736 := by exact prefixLift 5959736
  have htrace : WordTrace (prefixWord ++ tailWord_5959736) baseStart_5959736 baseEnd_5959736 := by
    simpa [prefixWord, tailWord_5959736, baseEnd_5959736] using wordTrace_append hprefix tailTrace_5959736
  have hstable : (prefixWord ++ tailWord_5959736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959736).length < 2 ^ (prefixWord ++ tailWord_5959736).sum := by decide
  have hdescent : baseEnd_5959736 < baseStart_5959736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959750 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_5959750 : Nat := 118140960795 + 5959750 * 2 ^ 59
def prefixEnd_5959750 : Nat := 4983230072969 + 3 ^ 40 * 5959750 * 2
def baseEnd_5959750 : Nat := 3060216330633162684416615

theorem tailTrace_5959750 : CollatzResearch.WordTrace tailWord_5959750 prefixEnd_5959750 3060216330633162684416615 := by
  unfold tailWord_5959750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6792810629964095909699647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144913293439234046073592469 6792810629964095909699647)
  ·
    refine ⟨10189215944946143864549471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6792810629964095909699647 10189215944946143864549471)
    ·
      refine ⟨15283823917419215796824207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10189215944946143864549471 15283823917419215796824207)
      ·
        refine ⟨22925735876128823695236311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15283823917419215796824207 22925735876128823695236311)
        ·
          refine ⟨34388603814193235542854467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22925735876128823695236311 34388603814193235542854467)
          ·
            refine ⟨51582905721289853314281701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34388603814193235542854467 51582905721289853314281701)
            ·
              refine ⟨9671794822741847496427819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51582905721289853314281701 9671794822741847496427819)
              ·
                refine ⟨14507692234112771244641729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671794822741847496427819 14507692234112771244641729)
                ·
                  refine ⟨10880769175584578433481297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14507692234112771244641729 10880769175584578433481297)
                  ·
                    refine ⟨8160576881688433825110973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10880769175584578433481297 8160576881688433825110973)
                    ·
                      refine ⟨3060216330633162684416615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8160576881688433825110973 3060216330633162684416615)
                      ·
                        rfl

theorem cell23_5959750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_5959750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959750 prefixEnd_5959750 := by exact prefixLift 5959750
  have htrace : WordTrace (prefixWord ++ tailWord_5959750) baseStart_5959750 baseEnd_5959750 := by
    simpa [prefixWord, tailWord_5959750, baseEnd_5959750] using wordTrace_append hprefix tailTrace_5959750
  have hstable : (prefixWord ++ tailWord_5959750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959750).length < 2 ^ (prefixWord ++ tailWord_5959750).sum := by decide
  have hdescent : baseEnd_5959750 < baseStart_5959750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959756 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 1, 5, 2]
def baseStart_5959756 : Nat := 118140960795 + 5959756 * 2 ^ 59
def prefixEnd_5959756 : Nat := 4983230072969 + 3 ^ 40 * 5959756 * 2
def baseEnd_5959756 : Nat := 3060219411517089660941587

theorem tailTrace_5959756 : CollatzResearch.WordTrace tailWord_5959756 prefixEnd_5959756 3060219411517089660941587 := by
  unfold tailWord_5959756
  simp only [CollatzResearch.WordTrace]
  refine ⟨108685079498414666067553561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144913439331219554756738081 108685079498414666067553561)
  ·
    refine ⟨81513809623810999550665171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108685079498414666067553561 81513809623810999550665171)
    ·
      refine ⟨122270714435716499325997757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81513809623810999550665171 122270714435716499325997757)
      ·
        refine ⟨45851517913393687247249159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122270714435716499325997757 45851517913393687247249159)
        ·
          refine ⟨68777276870090530870873739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45851517913393687247249159 68777276870090530870873739)
          ·
            refine ⟨103165915305135796306310609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68777276870090530870873739 103165915305135796306310609)
            ·
              refine ⟨77374436478851847229732957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103165915305135796306310609 77374436478851847229732957)
              ·
                refine ⟨29015413679569442711149859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77374436478851847229732957 29015413679569442711149859)
                ·
                  refine ⟨43523120519354164066724789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29015413679569442711149859 43523120519354164066724789)
                  ·
                    refine ⟨4080292548689452881255449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43523120519354164066724789 4080292548689452881255449)
                    ·
                      refine ⟨3060219411517089660941587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080292548689452881255449 3060219411517089660941587)
                      ·
                        rfl

theorem cell23_5959756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_5959756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959756 prefixEnd_5959756 := by exact prefixLift 5959756
  have htrace : WordTrace (prefixWord ++ tailWord_5959756) baseStart_5959756 baseEnd_5959756 := by
    simpa [prefixWord, tailWord_5959756, baseEnd_5959756] using wordTrace_append hprefix tailTrace_5959756
  have hstable : (prefixWord ++ tailWord_5959756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959756).length < 2 ^ (prefixWord ++ tailWord_5959756).sum := by decide
  have hdescent : baseEnd_5959756 < baseStart_5959756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959774 : List Nat := [4, 4, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_5959774 : Nat := 118140960795 + 5959774 * 2 ^ 59
def prefixEnd_5959774 : Nat := 4983230072969 + 3 ^ 40 * 5959774 * 2
def baseEnd_5959774 : Nat := 1020076218056290196838835

theorem tailTrace_5959774 : CollatzResearch.WordTrace tailWord_5959774 prefixEnd_5959774 1020076218056290196838835 := by
  unfold tailWord_5959774
  simp only [CollatzResearch.WordTrace]
  refine ⟨27171351938845515151157797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144913877007176080806174917 27171351938845515151157797)
  ·
    refine ⟨5094628488533534090842087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27171351938845515151157797 5094628488533534090842087)
    ·
      refine ⟨7641942732800301136263131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5094628488533534090842087 7641942732800301136263131)
      ·
        refine ⟨11462914099200451704394697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641942732800301136263131 11462914099200451704394697)
        ·
          refine ⟨8597185574400338778296023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11462914099200451704394697 8597185574400338778296023)
          ·
            refine ⟨12895778361600508167444035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8597185574400338778296023 12895778361600508167444035)
            ·
              refine ⟨19343667542400762251166053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12895778361600508167444035 19343667542400762251166053)
              ·
                refine ⟨3626937664200142922093635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19343667542400762251166053 3626937664200142922093635)
                ·
                  refine ⟨5440406496300214383140453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626937664200142922093635 5440406496300214383140453)
                  ·
                    refine ⟨1020076218056290196838835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440406496300214383140453 1020076218056290196838835)
                    ·
                      rfl

theorem cell23_5959774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_5959774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959774 prefixEnd_5959774 := by exact prefixLift 5959774
  have htrace : WordTrace (prefixWord ++ tailWord_5959774) baseStart_5959774 baseEnd_5959774 := by
    simpa [prefixWord, tailWord_5959774, baseEnd_5959774] using wordTrace_append hprefix tailTrace_5959774
  have hstable : (prefixWord ++ tailWord_5959774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959774).length < 2 ^ (prefixWord ++ tailWord_5959774).sum := by decide
  have hdescent : baseEnd_5959774 < baseStart_5959774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959837 : List Nat := [1, 4, 2, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_5959837 : Nat := 118140960795 + 5959837 * 2 ^ 59
def prefixEnd_5959837 : Nat := 4983230072969 + 3 ^ 40 * 5959837 * 2
def baseEnd_5959837 : Nat := 3060261003450103844028715

theorem tailTrace_5959837 : CollatzResearch.WordTrace tailWord_5959837 prefixEnd_5959837 3060261003450103844028715 := by
  unfold tailWord_5959837
  simp only [CollatzResearch.WordTrace]
  refine ⟨217373113309535882968805765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144915408873023921979203843 217373113309535882968805765)
  ·
    refine ⟨40757458745537978056651081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217373113309535882968805765 40757458745537978056651081)
    ·
      refine ⟨30568094059153483542488311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40757458745537978056651081 30568094059153483542488311)
      ·
        refine ⟨45852141088730225313732467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30568094059153483542488311 45852141088730225313732467)
        ·
          refine ⟨68778211633095337970598701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45852141088730225313732467 68778211633095337970598701)
          ·
            refine ⟨25791829362410751738974513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68778211633095337970598701 25791829362410751738974513)
            ·
              refine ⟨19343872021808063804230885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25791829362410751738974513 19343872021808063804230885)
              ·
                refine ⟨3626976004089011963293291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19343872021808063804230885 3626976004089011963293291)
                ·
                  refine ⟨5440464006133517944939937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3626976004089011963293291 5440464006133517944939937)
                  ·
                    refine ⟨4080348004600138458704953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5440464006133517944939937 4080348004600138458704953)
                    ·
                      refine ⟨3060261003450103844028715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080348004600138458704953 3060261003450103844028715)
                      ·
                        rfl

theorem cell23_5959837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_5959837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959837 prefixEnd_5959837 := by exact prefixLift 5959837
  have htrace : WordTrace (prefixWord ++ tailWord_5959837) baseStart_5959837 baseEnd_5959837 := by
    simpa [prefixWord, tailWord_5959837, baseEnd_5959837] using wordTrace_append hprefix tailTrace_5959837
  have hstable : (prefixWord ++ tailWord_5959837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959837).length < 2 ^ (prefixWord ++ tailWord_5959837).sum := by decide
  have hdescent : baseEnd_5959837 < baseStart_5959837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959847 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5959847 : Nat := 118140960795 + 5959847 * 2 ^ 59
def prefixEnd_5959847 : Nat := 4983230072969 + 3 ^ 40 * 5959847 * 2
def baseEnd_5959847 : Nat := 1020088712752216268301223

theorem tailTrace_5959847 : CollatzResearch.WordTrace tailWord_5959847 prefixEnd_5959847 1020088712752216268301223 := by
  unfold tailWord_5959847
  simp only [CollatzResearch.WordTrace]
  refine ⟨217373478039499654676669795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144915652026333103117779863 217373478039499654676669795)
  ·
    refine ⟨326060217059249482015004693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217373478039499654676669795 326060217059249482015004693)
    ·
      refine ⟨15284072674652319469453345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 326060217059249482015004693 15284072674652319469453345)
      ·
        refine ⟨11463054505989239602090009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15284072674652319469453345 11463054505989239602090009)
        ·
          refine ⟨8597290879491929701567507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11463054505989239602090009 8597290879491929701567507)
          ·
            refine ⟨12895936319237894552351261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8597290879491929701567507 12895936319237894552351261)
            ·
              refine ⟨4835976119714210457131723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12895936319237894552351261 4835976119714210457131723)
              ·
                refine ⟨7253964179571315685697585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835976119714210457131723 7253964179571315685697585)
                ·
                  refine ⟨5440473134678486764273189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7253964179571315685697585 5440473134678486764273189)
                  ·
                    refine ⟨1020088712752216268301223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440473134678486764273189 1020088712752216268301223)
                    ·
                      rfl

theorem cell23_5959847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5959847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959847 prefixEnd_5959847 := by exact prefixLift 5959847
  have htrace : WordTrace (prefixWord ++ tailWord_5959847) baseStart_5959847 baseEnd_5959847 := by
    simpa [prefixWord, tailWord_5959847, baseEnd_5959847] using wordTrace_append hprefix tailTrace_5959847
  have hstable : (prefixWord ++ tailWord_5959847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959847).length < 2 ^ (prefixWord ++ tailWord_5959847).sum := by decide
  have hdescent : baseEnd_5959847 < baseStart_5959847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959953 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 2, 5, 2]
def baseStart_5959953 : Nat := 118140960795 + 5959953 * 2 ^ 59
def prefixEnd_5959953 : Nat := 4983230072969 + 3 ^ 40 * 5959953 * 2
def baseEnd_5959953 : Nat := 3060320567206025390178181

theorem tailTrace_5959953 : CollatzResearch.WordTrace tailWord_5959953 prefixEnd_5959953 3060320567206025390178181 := by
  unfold tailWord_5959953
  simp only [CollatzResearch.WordTrace]
  refine ⟨217377344177115634780028513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144918229451410423186685675 217377344177115634780028513)
  ·
    refine ⟨163033008132836726085021385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217377344177115634780028513 163033008132836726085021385)
    ·
      refine ⟨122274756099627544563766039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163033008132836726085021385 122274756099627544563766039)
      ·
        refine ⟨183412134149441316845649059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122274756099627544563766039 183412134149441316845649059)
        ·
          refine ⟨275118201224161975268473589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183412134149441316845649059 275118201224161975268473589)
          ·
            refine ⟨25792331364765185181419399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 275118201224161975268473589 25792331364765185181419399)
            ·
              refine ⟨38688497047147777772129099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25792331364765185181419399 38688497047147777772129099)
              ·
                refine ⟨58032745570721666658193649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38688497047147777772129099 58032745570721666658193649)
                ·
                  refine ⟨43524559178041249993645237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58032745570721666658193649 43524559178041249993645237)
                  ·
                    refine ⟨4080427422941367186904241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43524559178041249993645237 4080427422941367186904241)
                    ·
                      refine ⟨3060320567206025390178181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080427422941367186904241 3060320567206025390178181)
                      ·
                        rfl

theorem cell23_5959953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_5959953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959953 prefixEnd_5959953 := by exact prefixLift 5959953
  have htrace : WordTrace (prefixWord ++ tailWord_5959953) baseStart_5959953 baseEnd_5959953 := by
    simpa [prefixWord, tailWord_5959953, baseEnd_5959953] using wordTrace_append hprefix tailTrace_5959953
  have hstable : (prefixWord ++ tailWord_5959953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959953).length < 2 ^ (prefixWord ++ tailWord_5959953).sum := by decide
  have hdescent : baseEnd_5959953 < baseStart_5959953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959983 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 4]
def baseStart_5959983 : Nat := 118140960795 + 5959983 * 2 ^ 59
def prefixEnd_5959983 : Nat := 4983230072969 + 3 ^ 40 * 5959983 * 2
def baseEnd_5959983 : Nat := 3060335971625660272803043

theorem tailTrace_5959983 : CollatzResearch.WordTrace tailWord_5959983 prefixEnd_5959983 3060335971625660272803043 := by
  unfold tailWord_5959983
  simp only [CollatzResearch.WordTrace]
  refine ⟨217378438367006949903620603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144918958911337966602413735 217378438367006949903620603)
  ·
    refine ⟨326067657550510424855430905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217378438367006949903620603 326067657550510424855430905)
    ·
      refine ⟨244550743162882818641573179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326067657550510424855430905 244550743162882818641573179)
      ·
        refine ⟨366826114744324227962359769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244550743162882818641573179 366826114744324227962359769)
        ·
          refine ⟨275119586058243170971769827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366826114744324227962359769 275119586058243170971769827)
          ·
            refine ⟨412679379087364756457654741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275119586058243170971769827 412679379087364756457654741)
            ·
              refine ⟨9672172947360111479476283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 412679379087364756457654741 9672172947360111479476283)
              ·
                refine ⟨14508259421040167219214425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9672172947360111479476283 14508259421040167219214425)
                ·
                  refine ⟨10881194565780125414410819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14508259421040167219214425 10881194565780125414410819)
                  ·
                    refine ⟨16321791848670188121616229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10881194565780125414410819 16321791848670188121616229)
                    ·
                      refine ⟨3060335971625660272803043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16321791848670188121616229 3060335971625660272803043)
                      ·
                        rfl

theorem cell23_5959983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_5959983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959983 prefixEnd_5959983 := by exact prefixLift 5959983
  have htrace : WordTrace (prefixWord ++ tailWord_5959983) baseStart_5959983 baseEnd_5959983 := by
    simpa [prefixWord, tailWord_5959983, baseEnd_5959983] using wordTrace_append hprefix tailTrace_5959983
  have hstable : (prefixWord ++ tailWord_5959983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959983).length < 2 ^ (prefixWord ++ tailWord_5959983).sum := by decide
  have hdescent : baseEnd_5959983 < baseStart_5959983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5959996 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5959996 : Nat := 118140960795 + 5959996 * 2 ^ 59
def prefixEnd_5959996 : Nat := 4983230072969 + 3 ^ 40 * 5959996 * 2
def baseEnd_5959996 : Nat := 3060342646874168721940483

theorem tailTrace_5959996 : CollatzResearch.WordTrace tailWord_5959996 prefixEnd_5959996 3060342646874168721940483 := by
  unfold tailWord_5959996
  simp only [CollatzResearch.WordTrace]
  refine ⟨108689456257979926561921921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144919275010639902082562561 108689456257979926561921921)
  ·
    refine ⟨81517092193484944921441441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108689456257979926561921921 81517092193484944921441441)
    ·
      refine ⟨61137819145113708691081081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81517092193484944921441441 61137819145113708691081081)
      ·
        refine ⟨45853364358835281518310811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61137819145113708691081081 45853364358835281518310811)
        ·
          refine ⟨68780046538252922277466217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45853364358835281518310811 68780046538252922277466217)
          ·
            refine ⟨51585034903689691708099663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68780046538252922277466217 51585034903689691708099663)
            ·
              refine ⟨77377552355534537562149495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51585034903689691708099663 77377552355534537562149495)
              ·
                refine ⟨116066328533301806343224243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77377552355534537562149495 116066328533301806343224243)
                ·
                  refine ⟨174099492799952709514836365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116066328533301806343224243 174099492799952709514836365)
                  ·
                    refine ⟨65287309799982266068063637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174099492799952709514836365 65287309799982266068063637)
                    ·
                      refine ⟨3060342646874168721940483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65287309799982266068063637 3060342646874168721940483)
                      ·
                        rfl

theorem cell23_5959996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5959996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5959996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5959996 prefixEnd_5959996 := by exact prefixLift 5959996
  have htrace : WordTrace (prefixWord ++ tailWord_5959996) baseStart_5959996 baseEnd_5959996 := by
    simpa [prefixWord, tailWord_5959996, baseEnd_5959996] using wordTrace_append hprefix tailTrace_5959996
  have hstable : (prefixWord ++ tailWord_5959996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5959996).length < 2 ^ (prefixWord ++ tailWord_5959996).sum := by decide
  have hdescent : baseEnd_5959996 < baseStart_5959996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5959996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960003 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 3]
def baseStart_5960003 : Nat := 118140960795 + 5960003 * 2 ^ 59
def prefixEnd_5960003 : Nat := 4983230072969 + 3 ^ 40 * 5960003 * 2
def baseEnd_5960003 : Nat := 3060346241238750194552951

theorem tailTrace_5960003 : CollatzResearch.WordTrace tailWord_5960003 prefixEnd_5960003 3060346241238750194552951 := by
  unfold tailWord_5960003
  simp only [CollatzResearch.WordTrace]
  refine ⟨217379167826934493319348663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144919445217956328879565775 217379167826934493319348663)
  ·
    refine ⟨326068751740401739979022995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217379167826934493319348663 326068751740401739979022995)
    ·
      refine ⟨489103127610602609968534493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326068751740401739979022995 489103127610602609968534493)
      ·
        refine ⟨183413672853975978738200435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489103127610602609968534493 183413672853975978738200435)
        ·
          refine ⟨275120509280963968107300653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183413672853975978738200435 275120509280963968107300653)
          ·
            refine ⟨103170190980361488040237745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275120509280963968107300653 103170190980361488040237745)
            ·
              refine ⟨77377643235271116030178309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103170190980361488040237745 77377643235271116030178309)
              ·
                refine ⟨14508308106613334255658433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77377643235271116030178309 14508308106613334255658433)
                ·
                  refine ⟨10881231079960000691743825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14508308106613334255658433 10881231079960000691743825)
                  ·
                    refine ⟨8160923309970000518807869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10881231079960000691743825 8160923309970000518807869)
                    ·
                      refine ⟨3060346241238750194552951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8160923309970000518807869 3060346241238750194552951)
                      ·
                        rfl

theorem cell23_5960003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_5960003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960003 prefixEnd_5960003 := by exact prefixLift 5960003
  have htrace : WordTrace (prefixWord ++ tailWord_5960003) baseStart_5960003 baseEnd_5960003 := by
    simpa [prefixWord, tailWord_5960003, baseEnd_5960003] using wordTrace_append hprefix tailTrace_5960003
  have hstable : (prefixWord ++ tailWord_5960003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960003).length < 2 ^ (prefixWord ++ tailWord_5960003).sum := by decide
  have hdescent : baseEnd_5960003 < baseStart_5960003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960026 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_5960026 : Nat := 118140960795 + 5960026 * 2 ^ 59
def prefixEnd_5960026 : Nat := 4983230072969 + 3 ^ 40 * 5960026 * 2
def baseEnd_5960026 : Nat := 3060358051293803604565345

theorem tailTrace_5960026 : CollatzResearch.WordTrace tailWord_5960026 prefixEnd_5960026 3060358051293803604565345 := by
  unfold tailWord_5960026
  simp only [CollatzResearch.WordTrace]
  refine ⟨54345001676462792061858983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144920004470567445498290621 54345001676462792061858983)
  ·
    refine ⟨81517502514694188092788475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54345001676462792061858983 81517502514694188092788475)
    ·
      refine ⟨122276253772041282139182713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81517502514694188092788475 122276253772041282139182713)
      ·
        refine ⟨91707190329030961604387035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122276253772041282139182713 91707190329030961604387035)
        ·
          refine ⟨137560785493546442406580553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91707190329030961604387035 137560785493546442406580553)
          ·
            refine ⟨103170589120159831804935415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137560785493546442406580553 103170589120159831804935415)
            ·
              refine ⟨154755883680239747707403123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103170589120159831804935415 154755883680239747707403123)
              ·
                refine ⟨232133825520359621561104685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154755883680239747707403123 232133825520359621561104685)
                ·
                  refine ⟨87050184570134858085414257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232133825520359621561104685 87050184570134858085414257)
                  ·
                    refine ⟨65287638427601143564060693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87050184570134858085414257 65287638427601143564060693)
                    ·
                      refine ⟨3060358051293803604565345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65287638427601143564060693 3060358051293803604565345)
                      ·
                        rfl

theorem cell23_5960026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_5960026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960026 prefixEnd_5960026 := by exact prefixLift 5960026
  have htrace : WordTrace (prefixWord ++ tailWord_5960026) baseStart_5960026 baseEnd_5960026 := by
    simpa [prefixWord, tailWord_5960026, baseEnd_5960026] using wordTrace_append hprefix tailTrace_5960026
  have hstable : (prefixWord ++ tailWord_5960026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960026).length < 2 ^ (prefixWord ++ tailWord_5960026).sum := by decide
  have hdescent : baseEnd_5960026 < baseStart_5960026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960044 : List Nat := [2, 2, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_5960044 : Nat := 118140960795 + 5960044 * 2 ^ 59
def prefixEnd_5960044 : Nat := 4983230072969 + 3 ^ 40 * 5960044 * 2
def baseEnd_5960044 : Nat := 1020122431315194844713421

theorem tailTrace_5960044 : CollatzResearch.WordTrace tailWord_5960044 prefixEnd_5960044 1020122431315194844713421 := by
  unfold tailWord_5960044
  simp only [CollatzResearch.WordTrace]
  refine ⟨108690331609892978660795593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144920442146523971547727457 108690331609892978660795593)
  ·
    refine ⟨81517748707419733995596695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108690331609892978660795593 81517748707419733995596695)
    ·
      refine ⟨122276623061129600993395043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81517748707419733995596695 122276623061129600993395043)
      ·
        refine ⟨183414934591694401490092565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122276623061129600993395043 183414934591694401490092565)
        ·
          refine ⟨8597575058985675069848089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183414934591694401490092565 8597575058985675069848089)
          ·
            refine ⟨6448181294239256302386067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8597575058985675069848089 6448181294239256302386067)
            ·
              refine ⟨9672271941358884453579101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448181294239256302386067 9672271941358884453579101)
              ·
                refine ⟨3627101978009581670092163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9672271941358884453579101 3627101978009581670092163)
                ·
                  refine ⟨5440652967014372505138245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627101978009581670092163 5440652967014372505138245)
                  ·
                    refine ⟨1020122431315194844713421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440652967014372505138245 1020122431315194844713421)
                    ·
                      rfl

theorem cell23_5960044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_5960044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960044 prefixEnd_5960044 := by exact prefixLift 5960044
  have htrace : WordTrace (prefixWord ++ tailWord_5960044) baseStart_5960044 baseEnd_5960044 := by
    simpa [prefixWord, tailWord_5960044, baseEnd_5960044] using wordTrace_append hprefix tailTrace_5960044
  have hstable : (prefixWord ++ tailWord_5960044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960044).length < 2 ^ (prefixWord ++ tailWord_5960044).sum := by decide
  have hdescent : baseEnd_5960044 < baseStart_5960044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960054 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5960054 : Nat := 118140960795 + 5960054 * 2 ^ 59
def prefixEnd_5960054 : Nat := 4983230072969 + 3 ^ 40 * 5960054 * 2
def baseEnd_5960054 : Nat := 3060372428752129495015217

theorem tailTrace_5960054 : CollatzResearch.WordTrace tailWord_5960054 prefixEnd_5960054 3060372428752129495015217 := by
  unfold tailWord_5960054
  simp only [CollatzResearch.WordTrace]
  refine ⟨13586314246859358064340951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144920685299833152686303477 13586314246859358064340951)
  ·
    refine ⟨20379471370289037096511427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13586314246859358064340951 20379471370289037096511427)
    ·
      refine ⟨30569207055433555644767141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20379471370289037096511427 30569207055433555644767141)
      ·
        refine ⟨5731726322893791683393839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30569207055433555644767141 5731726322893791683393839)
        ·
          refine ⟨8597589484340687525090759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731726322893791683393839 8597589484340687525090759)
          ·
            refine ⟨12896384226511031287636139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8597589484340687525090759 12896384226511031287636139)
            ·
              refine ⟨19344576339766546931454209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12896384226511031287636139 19344576339766546931454209)
              ·
                refine ⟨14508432254824910198590657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19344576339766546931454209 14508432254824910198590657)
                ·
                  refine ⟨10881324191118682648942993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14508432254824910198590657 10881324191118682648942993)
                  ·
                    refine ⟨8160993143339011986707245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10881324191118682648942993 8160993143339011986707245)
                    ·
                      refine ⟨3060372428752129495015217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8160993143339011986707245 3060372428752129495015217)
                      ·
                        rfl

theorem cell23_5960054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5960054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960054 prefixEnd_5960054 := by exact prefixLift 5960054
  have htrace : WordTrace (prefixWord ++ tailWord_5960054) baseStart_5960054 baseEnd_5960054 := by
    simpa [prefixWord, tailWord_5960054, baseEnd_5960054] using wordTrace_append hprefix tailTrace_5960054
  have hstable : (prefixWord ++ tailWord_5960054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960054).length < 2 ^ (prefixWord ++ tailWord_5960054).sum := by decide
  have hdescent : baseEnd_5960054 < baseStart_5960054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960074 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 6]
def baseStart_5960074 : Nat := 118140960795 + 5960074 * 2 ^ 59
def prefixEnd_5960074 : Nat := 4983230072969 + 3 ^ 40 * 5960074 * 2
def baseEnd_5960074 : Nat := 340042522040579935196125

theorem tailTrace_5960074 : CollatzResearch.WordTrace tailWord_5960074 prefixEnd_5960074 340042522040579935196125 := by
  unfold tailWord_5960074
  simp only [CollatzResearch.WordTrace]
  refine ⟨54345439352419318111295819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144921171606451514963455517 54345439352419318111295819)
  ·
    refine ⟨81518159028628977166943729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54345439352419318111295819 81518159028628977166943729)
    ·
      refine ⟨61138619271471732875207797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81518159028628977166943729 61138619271471732875207797)
      ·
        refine ⟨5731745556700474957050731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61138619271471732875207797 5731745556700474957050731)
        ·
          refine ⟨8597618335050712435576097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5731745556700474957050731 8597618335050712435576097)
          ·
            refine ⟨6448213751288034326682073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8597618335050712435576097 6448213751288034326682073)
            ·
              refine ⟨4836160313466025745011555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6448213751288034326682073 4836160313466025745011555)
              ·
                refine ⟨7254240470199038617517333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836160313466025745011555 7254240470199038617517333)
                ·
                  refine ⟨340042522040579935196125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7254240470199038617517333 340042522040579935196125)
                  ·
                    rfl

theorem cell23_5960074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_5960074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960074 prefixEnd_5960074 := by exact prefixLift 5960074
  have htrace : WordTrace (prefixWord ++ tailWord_5960074) baseStart_5960074 baseEnd_5960074 := by
    simpa [prefixWord, tailWord_5960074, baseEnd_5960074] using wordTrace_append hprefix tailTrace_5960074
  have hstable : (prefixWord ++ tailWord_5960074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960074).length < 2 ^ (prefixWord ++ tailWord_5960074).sum := by decide
  have hdescent : baseEnd_5960074 < baseStart_5960074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960090 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_5960090 : Nat := 118140960795 + 5960090 * 2 ^ 59
def prefixEnd_5960090 : Nat := 4983230072969 + 3 ^ 40 * 5960090 * 2
def baseEnd_5960090 : Nat := 3060390914055691354165051

theorem tailTrace_5960090 : CollatzResearch.WordTrace tailWord_5960090 prefixEnd_5960090 3060390914055691354165051 := by
  unfold tailWord_5960090
  simp only [CollatzResearch.WordTrace]
  refine ⟨54345585244404826794441431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144921560651746204785177149 54345585244404826794441431)
  ·
    refine ⟨81518377866607240191662147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54345585244404826794441431 81518377866607240191662147)
    ·
      refine ⟨122277566799910860287493221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81518377866607240191662147 122277566799910860287493221)
      ·
        refine ⟨22927043774983286303904979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122277566799910860287493221 22927043774983286303904979)
        ·
          refine ⟨34390565662474929455857469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22927043774983286303904979 34390565662474929455857469)
          ·
            refine ⟨12896462123428098545946551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34390565662474929455857469 12896462123428098545946551)
            ·
              refine ⟨19344693185142147818919827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12896462123428098545946551 19344693185142147818919827)
              ·
                refine ⟨29017039777713221728379741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19344693185142147818919827 29017039777713221728379741)
                ·
                  refine ⟨10881389916642458148142403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29017039777713221728379741 10881389916642458148142403)
                  ·
                    refine ⟨16322084874963687222213605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10881389916642458148142403 16322084874963687222213605)
                    ·
                      refine ⟨3060390914055691354165051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16322084874963687222213605 3060390914055691354165051)
                      ·
                        rfl

theorem cell23_5960090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_5960090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960090 prefixEnd_5960090 := by exact prefixLift 5960090
  have htrace : WordTrace (prefixWord ++ tailWord_5960090) baseStart_5960090 baseEnd_5960090 := by
    simpa [prefixWord, tailWord_5960090, baseEnd_5960090] using wordTrace_append hprefix tailTrace_5960090
  have hstable : (prefixWord ++ tailWord_5960090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960090).length < 2 ^ (prefixWord ++ tailWord_5960090).sum := by decide
  have hdescent : baseEnd_5960090 < baseStart_5960090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960094 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5960094 : Nat := 118140960795 + 5960094 * 2 ^ 59
def prefixEnd_5960094 : Nat := 4983230072969 + 3 ^ 40 * 5960094 * 2
def baseEnd_5960094 : Nat := 3060392967978309338515033

theorem tailTrace_5960094 : CollatzResearch.WordTrace tailWord_5960094 prefixEnd_5960094 3060392967978309338515033 := by
  unfold tailWord_5960094
  simp only [CollatzResearch.WordTrace]
  refine ⟨27172810858700601982613917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144921657913069877240607557 27172810858700601982613917)
  ·
    refine ⟨10189804072012725743480219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27172810858700601982613917 10189804072012725743480219)
    ·
      refine ⟨15284706108019088615220329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10189804072012725743480219 15284706108019088615220329)
      ·
        refine ⟨11463529581014316461415247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15284706108019088615220329 11463529581014316461415247)
        ·
          refine ⟨17195294371521474692122871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11463529581014316461415247 17195294371521474692122871)
          ·
            refine ⟨25792941557282212038184307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17195294371521474692122871 25792941557282212038184307)
            ·
              refine ⟨38689412335923318057276461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25792941557282212038184307 38689412335923318057276461)
              ·
                refine ⟨14508529625971244271478673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38689412335923318057276461 14508529625971244271478673)
                ·
                  refine ⟨10881397219478433203609005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14508529625971244271478673 10881397219478433203609005)
                  ·
                    refine ⟨4080523957304412451353377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10881397219478433203609005 4080523957304412451353377)
                    ·
                      refine ⟨3060392967978309338515033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080523957304412451353377 3060392967978309338515033)
                      ·
                        rfl

theorem cell23_5960094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5960094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960094 prefixEnd_5960094 := by exact prefixLift 5960094
  have htrace : WordTrace (prefixWord ++ tailWord_5960094) baseStart_5960094 baseEnd_5960094 := by
    simpa [prefixWord, tailWord_5960094, baseEnd_5960094] using wordTrace_append hprefix tailTrace_5960094
  have hstable : (prefixWord ++ tailWord_5960094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960094).length < 2 ^ (prefixWord ++ tailWord_5960094).sum := by decide
  have hdescent : baseEnd_5960094 < baseStart_5960094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960104 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5960104 : Nat := 118140960795 + 5960104 * 2 ^ 59
def prefixEnd_5960104 : Nat := 4983230072969 + 3 ^ 40 * 5960104 * 2
def baseEnd_5960104 : Nat := 1020132700928284766463329

theorem tailTrace_5960104 : CollatzResearch.WordTrace tailWord_5960104 prefixEnd_5960104 1020132700928284766463329 := by
  unfold tailWord_5960104
  simp only [CollatzResearch.WordTrace]
  refine ⟨108691425799784293784387683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144921901066379058379183577 108691425799784293784387683)
  ·
    refine ⟨163037138699676440676581525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108691425799784293784387683 163037138699676440676581525)
    ·
      refine ⟨7642365876547333156714759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163037138699676440676581525 7642365876547333156714759)
      ·
        refine ⟨11463548814820999735072139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7642365876547333156714759 11463548814820999735072139)
        ·
          refine ⟨17195323222231499602608209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11463548814820999735072139 17195323222231499602608209)
          ·
            refine ⟨12896492416673624701956157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17195323222231499602608209 12896492416673624701956157)
            ·
              refine ⟨4836184656252609263233559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12896492416673624701956157 4836184656252609263233559)
              ·
                refine ⟨7254276984378913894850339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836184656252609263233559 7254276984378913894850339)
                ·
                  refine ⟨10881415476568370842275509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7254276984378913894850339 10881415476568370842275509)
                  ·
                    refine ⟨1020132700928284766463329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10881415476568370842275509 1020132700928284766463329)
                    ·
                      rfl

theorem cell23_5960104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5960104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960104 prefixEnd_5960104 := by exact prefixLift 5960104
  have htrace : WordTrace (prefixWord ++ tailWord_5960104) baseStart_5960104 baseEnd_5960104 := by
    simpa [prefixWord, tailWord_5960104, baseEnd_5960104] using wordTrace_append hprefix tailTrace_5960104
  have hstable : (prefixWord ++ tailWord_5960104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960104).length < 2 ^ (prefixWord ++ tailWord_5960104).sum := by decide
  have hdescent : baseEnd_5960104 < baseStart_5960104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960153 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_5960153 : Nat := 118140960795 + 5960153 * 2 ^ 59
def prefixEnd_5960153 : Nat := 4983230072969 + 3 ^ 40 * 5960153 * 2
def baseEnd_5960153 : Nat := 3060423263336924607677261

theorem tailTrace_5960153 : CollatzResearch.WordTrace tailWord_5960153 prefixEnd_5960153 3060423263336924607677261 := by
  unfold tailWord_5960153
  simp only [CollatzResearch.WordTrace]
  refine ⟨217384638776391068937309113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144923092517594045958206075 217384638776391068937309113)
  ·
    refine ⟨163038479082293301702981835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217384638776391068937309113 163038479082293301702981835)
    ·
      refine ⟨244557718623439952554472753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163038479082293301702981835 244557718623439952554472753)
      ·
        refine ⟨183418288967579964415854565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244557718623439952554472753 183418288967579964415854565)
        ·
          refine ⟨34390929181421243327972731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183418288967579964415854565 34390929181421243327972731)
          ·
            refine ⟨51586393772131864991959097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34390929181421243327972731 51586393772131864991959097)
            ·
              refine ⟨38689795329098898743969323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51586393772131864991959097 38689795329098898743969323)
              ·
                refine ⟨58034692993648348115953985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38689795329098898743969323 58034692993648348115953985)
                ·
                  refine ⟨43526019745236261086965489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58034692993648348115953985 43526019745236261086965489)
                  ·
                    refine ⟨32644514808927195815224117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43526019745236261086965489 32644514808927195815224117)
                    ·
                      refine ⟨3060423263336924607677261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32644514808927195815224117 3060423263336924607677261)
                      ·
                        rfl

theorem cell23_5960153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_5960153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960153 prefixEnd_5960153 := by exact prefixLift 5960153
  have htrace : WordTrace (prefixWord ++ tailWord_5960153) baseStart_5960153 baseEnd_5960153 := by
    simpa [prefixWord, tailWord_5960153, baseEnd_5960153] using wordTrace_append hprefix tailTrace_5960153
  have hstable : (prefixWord ++ tailWord_5960153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960153).length < 2 ^ (prefixWord ++ tailWord_5960153).sum := by decide
  have hdescent : baseEnd_5960153 < baseStart_5960153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960157 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5960157 : Nat := 118140960795 + 5960157 * 2 ^ 59
def prefixEnd_5960157 : Nat := 4983230072969 + 3 ^ 40 * 5960157 * 2
def baseEnd_5960157 : Nat := 3060425317259542592027243

theorem tailTrace_5960157 : CollatzResearch.WordTrace tailWord_5960157 prefixEnd_5960157 3060425317259542592027243 := by
  unfold tailWord_5960157
  simp only [CollatzResearch.WordTrace]
  refine ⟨217384784668376577620454725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144923189778917718413636483 217384784668376577620454725)
  ·
    refine ⟨40759647125320608303835261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217384784668376577620454725 40759647125320608303835261)
    ·
      refine ⟨15284867671995228113938223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40759647125320608303835261 15284867671995228113938223)
      ·
        refine ⟨22927301507992842170907335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15284867671995228113938223 22927301507992842170907335)
        ·
          refine ⟨34390952261989263256361003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22927301507992842170907335 34390952261989263256361003)
          ·
            refine ⟨51586428392983894884541505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34390952261989263256361003 51586428392983894884541505)
            ·
              refine ⟨38689821294737921163406129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51586428392983894884541505 38689821294737921163406129)
              ·
                refine ⟨29017365971053440872554597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38689821294737921163406129 29017365971053440872554597)
                ·
                  refine ⟨5440756119572520163603987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29017365971053440872554597 5440756119572520163603987)
                  ·
                    refine ⟨8161134179358780245405981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5440756119572520163603987 8161134179358780245405981)
                    ·
                      refine ⟨3060425317259542592027243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161134179358780245405981 3060425317259542592027243)
                      ·
                        rfl

theorem cell23_5960157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5960157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960157 prefixEnd_5960157 := by exact prefixLift 5960157
  have htrace : WordTrace (prefixWord ++ tailWord_5960157) baseStart_5960157 baseEnd_5960157 := by
    simpa [prefixWord, tailWord_5960157, baseEnd_5960157] using wordTrace_append hprefix tailTrace_5960157
  have hstable : (prefixWord ++ tailWord_5960157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960157).length < 2 ^ (prefixWord ++ tailWord_5960157).sum := by decide
  have hdescent : baseEnd_5960157 < baseStart_5960157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960174 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_5960174 : Nat := 118140960795 + 5960174 * 2 ^ 59
def prefixEnd_5960174 : Nat := 4983230072969 + 3 ^ 40 * 5960174 * 2
def baseEnd_5960174 : Nat := 3060434046430669025514665

theorem tailTrace_5960174 : CollatzResearch.WordTrace tailWord_5960174 prefixEnd_5960174 3060434046430669025514665 := by
  unfold tailWord_5960174
  simp only [CollatzResearch.WordTrace]
  refine ⟨27173175588664373690477947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144923603139543326349215717 27173175588664373690477947)
  ·
    refine ⟨40759763382996560535716921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27173175588664373690477947 40759763382996560535716921)
    ·
      refine ⟨30569822537247420401787691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40759763382996560535716921 30569822537247420401787691)
      ·
        refine ⟨45854733805871130602681537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30569822537247420401787691 45854733805871130602681537)
        ·
          refine ⟨34391050354403347952011153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45854733805871130602681537 34391050354403347952011153)
          ·
            refine ⟨25793287765802510964008365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34391050354403347952011153 25793287765802510964008365)
            ·
              refine ⟨9672482912175941611503137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25793287765802510964008365 9672482912175941611503137)
              ·
                refine ⟨7254362184131956208627353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9672482912175941611503137 7254362184131956208627353)
                ·
                  refine ⟨5440771638098967156470515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7254362184131956208627353 5440771638098967156470515)
                  ·
                    refine ⟨8161157457148450734705773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5440771638098967156470515 8161157457148450734705773)
                    ·
                      refine ⟨3060434046430669025514665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161157457148450734705773 3060434046430669025514665)
                      ·
                        rfl

theorem cell23_5960174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_5960174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960174 prefixEnd_5960174 := by exact prefixLift 5960174
  have htrace : WordTrace (prefixWord ++ tailWord_5960174) baseStart_5960174 baseEnd_5960174 := by
    simpa [prefixWord, tailWord_5960174, baseEnd_5960174] using wordTrace_append hprefix tailTrace_5960174
  have hstable : (prefixWord ++ tailWord_5960174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960174).length < 2 ^ (prefixWord ++ tailWord_5960174).sum := by decide
  have hdescent : baseEnd_5960174 < baseStart_5960174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960197 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 1, 4, 2]
def baseStart_5960197 : Nat := 118140960795 + 5960197 * 2 ^ 59
def prefixEnd_5960197 : Nat := 4983230072969 + 3 ^ 40 * 5960197 * 2
def baseEnd_5960197 : Nat := 3060445856485722435527059

theorem tailTrace_5960197 : CollatzResearch.WordTrace tailWord_5960197 prefixEnd_5960197 3060445856485722435527059 := by
  unfold tailWord_5960197
  simp only [CollatzResearch.WordTrace]
  refine ⟨217386243588231664451910845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144924162392154442967940563 217386243588231664451910845)
  ·
    refine ⟨81519841345586874169466567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217386243588231664451910845 81519841345586874169466567)
    ·
      refine ⟨122279762018380311254199851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81519841345586874169466567 122279762018380311254199851)
      ·
        refine ⟨183419643027570466881299777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122279762018380311254199851 183419643027570466881299777)
        ·
          refine ⟨137564732270677850160974833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183419643027570466881299777 137564732270677850160974833)
          ·
            refine ⟨103173549203008387620731125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137564732270677850160974833 103173549203008387620731125)
            ·
              refine ⟨9672520237782036339443543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103173549203008387620731125 9672520237782036339443543)
              ·
                refine ⟨14508780356673054509165315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9672520237782036339443543 14508780356673054509165315)
                ·
                  refine ⟨21763170535009581763747973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14508780356673054509165315 21763170535009581763747973)
                  ·
                    refine ⟨4080594475314296580702745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21763170535009581763747973 4080594475314296580702745)
                    ·
                      refine ⟨3060445856485722435527059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080594475314296580702745 3060445856485722435527059)
                      ·
                        rfl

theorem cell23_5960197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_5960197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960197 prefixEnd_5960197 := by exact prefixLift 5960197
  have htrace : WordTrace (prefixWord ++ tailWord_5960197) baseStart_5960197 baseEnd_5960197 := by
    simpa [prefixWord, tailWord_5960197, baseEnd_5960197] using wordTrace_append hprefix tailTrace_5960197
  have hstable : (prefixWord ++ tailWord_5960197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960197).length < 2 ^ (prefixWord ++ tailWord_5960197).sum := by decide
  have hdescent : baseEnd_5960197 < baseStart_5960197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960270 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_5960270 : Nat := 118140960795 + 5960270 * 2 ^ 59
def prefixEnd_5960270 : Nat := 4983230072969 + 3 ^ 40 * 5960270 * 2
def baseEnd_5960270 : Nat := 3060483340573500649914223

theorem tailTrace_5960270 : CollatzResearch.WordTrace tailWord_5960270 prefixEnd_5960270 3060483340573500649914223 := by
  unfold tailWord_5960270
  simp only [CollatzResearch.WordTrace]
  refine ⟨27173613264620899739914783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144925937411311465279545509 27173613264620899739914783)
  ·
    refine ⟨40760419896931349609872175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27173613264620899739914783 40760419896931349609872175)
    ·
      refine ⟨61140629845397024414808263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40760419896931349609872175 61140629845397024414808263)
      ·
        refine ⟨91710944768095536622212395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61140629845397024414808263 91710944768095536622212395)
        ·
          refine ⟨137566417152143304933318593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91710944768095536622212395 137566417152143304933318593)
          ·
            refine ⟨103174812864107478699988945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137566417152143304933318593 103174812864107478699988945)
            ·
              refine ⟨77381109648080609024991709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103174812864107478699988945 77381109648080609024991709)
              ·
                refine ⟨29017916118030228384371891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77381109648080609024991709 29017916118030228384371891)
                ·
                  refine ⟨43526874177045342576557837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29017916118030228384371891 43526874177045342576557837)
                  ·
                    refine ⟨16322577816392003466209189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43526874177045342576557837 16322577816392003466209189)
                    ·
                      refine ⟨3060483340573500649914223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16322577816392003466209189 3060483340573500649914223)
                      ·
                        rfl

theorem cell23_5960270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_5960270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960270 prefixEnd_5960270 := by exact prefixLift 5960270
  have htrace : WordTrace (prefixWord ++ tailWord_5960270) baseStart_5960270 baseEnd_5960270 := by
    simpa [prefixWord, tailWord_5960270, baseEnd_5960270] using wordTrace_append hprefix tailTrace_5960270
  have hstable : (prefixWord ++ tailWord_5960270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960270).length < 2 ^ (prefixWord ++ tailWord_5960270).sum := by decide
  have hdescent : baseEnd_5960270 < baseStart_5960270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960304 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 2, 4, 2]
def baseStart_5960304 : Nat := 118140960795 + 5960304 * 2 ^ 59
def prefixEnd_5960304 : Nat := 4983230072969 + 3 ^ 40 * 5960304 * 2
def baseEnd_5960304 : Nat := 3060500798915753516889067

theorem tailTrace_5960304 : CollatzResearch.WordTrace tailWord_5960304 prefixEnd_5960304 3060500798915753516889067 := by
  unfold tailWord_5960304
  simp only [CollatzResearch.WordTrace]
  refine ⟨108695073099422010863027983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144926764132562681150703977 108695073099422010863027983)
  ·
    refine ⟨163042609649133016294541975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108695073099422010863027983 163042609649133016294541975)
    ·
      refine ⟨244563914473699524441812963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163042609649133016294541975 244563914473699524441812963)
      ·
        refine ⟨366845871710549286662719445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244563914473699524441812963 366845871710549286662719445)
        ·
          refine ⟨8597950118215998906157487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 366845871710549286662719445 8597950118215998906157487)
          ·
            refine ⟨12896925177323998359236231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8597950118215998906157487 12896925177323998359236231)
            ·
              refine ⟨19345387765985997538854347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12896925177323998359236231 19345387765985997538854347)
              ·
                refine ⟨29018081648978996308281521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19345387765985997538854347 29018081648978996308281521)
                ·
                  refine ⟨21763561236734247231211141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29018081648978996308281521 21763561236734247231211141)
                  ·
                    refine ⟨4080667731887671355852089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21763561236734247231211141 4080667731887671355852089)
                    ·
                      refine ⟨3060500798915753516889067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080667731887671355852089 3060500798915753516889067)
                      ·
                        rfl

theorem cell23_5960304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 4, 2].length) (baseStart_5960304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960304 prefixEnd_5960304 := by exact prefixLift 5960304
  have htrace : WordTrace (prefixWord ++ tailWord_5960304) baseStart_5960304 baseEnd_5960304 := by
    simpa [prefixWord, tailWord_5960304, baseEnd_5960304] using wordTrace_append hprefix tailTrace_5960304
  have hstable : (prefixWord ++ tailWord_5960304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960304).length < 2 ^ (prefixWord ++ tailWord_5960304).sum := by decide
  have hdescent : baseEnd_5960304 < baseStart_5960304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960324 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_5960324 : Nat := 118140960795 + 5960324 * 2 ^ 59
def prefixEnd_5960324 : Nat := 4983230072969 + 3 ^ 40 * 5960324 * 2
def baseEnd_5960324 : Nat := 3060511068528843438638975

theorem tailTrace_5960324 : CollatzResearch.WordTrace tailWord_5960324 prefixEnd_5960324 3060511068528843438638975 := by
  unfold tailWord_5960324
  simp only [CollatzResearch.WordTrace]
  refine ⟨108695437829385782570892013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144927250439181043427856017 108695437829385782570892013)
  ·
    refine ⟨40760789186019668464084505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108695437829385782570892013 40760789186019668464084505)
    ·
      refine ⟨30570591889514751348063379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40760789186019668464084505 30570591889514751348063379)
      ·
        refine ⟨45855887834272127022095069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30570591889514751348063379 45855887834272127022095069)
        ·
          refine ⟨17195957937852047633285651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45855887834272127022095069 17195957937852047633285651)
          ·
            refine ⟨25793936906778071449928477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17195957937852047633285651 25793936906778071449928477)
            ·
              refine ⟨9672726340041776793723179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25793936906778071449928477 9672726340041776793723179)
              ·
                refine ⟨14509089510062665190584769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9672726340041776793723179 14509089510062665190584769)
                ·
                  refine ⟨10881817132546998892938577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14509089510062665190584769 10881817132546998892938577)
                  ·
                    refine ⟨8161362849410249169703933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10881817132546998892938577 8161362849410249169703933)
                    ·
                      refine ⟨3060511068528843438638975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161362849410249169703933 3060511068528843438638975)
                      ·
                        rfl

theorem cell23_5960324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_5960324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960324 prefixEnd_5960324 := by exact prefixLift 5960324
  have htrace : WordTrace (prefixWord ++ tailWord_5960324) baseStart_5960324 baseEnd_5960324 := by
    simpa [prefixWord, tailWord_5960324, baseEnd_5960324] using wordTrace_append hprefix tailTrace_5960324
  have hstable : (prefixWord ++ tailWord_5960324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960324).length < 2 ^ (prefixWord ++ tailWord_5960324).sum := by decide
  have hdescent : baseEnd_5960324 < baseStart_5960324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960347 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 8, 3, 2]
def baseStart_5960347 : Nat := 118140960795 + 5960347 * 2 ^ 59
def prefixEnd_5960347 : Nat := 4983230072969 + 3 ^ 40 * 5960347 * 2
def baseEnd_5960347 : Nat := 3060522878583896848651369

theorem tailTrace_5960347 : CollatzResearch.WordTrace tailWord_5960347 prefixEnd_5960347 3060522878583896848651369 := by
  unfold tailWord_5960347
  simp only [CollatzResearch.WordTrace]
  refine ⟨217391714537688240069871295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144927809691792160046580863 217391714537688240069871295)
  ·
    refine ⟨326087571806532360104806943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217391714537688240069871295 326087571806532360104806943)
    ·
      refine ⟨489131357709798540157210415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326087571806532360104806943 489131357709798540157210415)
      ·
        refine ⟨733697036564697810235815623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489131357709798540157210415 733697036564697810235815623)
        ·
          refine ⟨1100545554847046715353723435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733697036564697810235815623 1100545554847046715353723435)
          ·
            refine ⟨1650818332270570073030585153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100545554847046715353723435 1650818332270570073030585153)
            ·
              refine ⟨1238113749202927554772938865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650818332270570073030585153 1238113749202927554772938865)
              ·
                refine ⟨928585311902195666079704149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238113749202927554772938865 928585311902195666079704149)
                ·
                  refine ⟨10881859123853855461871533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 928585311902195666079704149 10881859123853855461871533)
                  ·
                    refine ⟨4080697171445195798201825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10881859123853855461871533 4080697171445195798201825)
                    ·
                      refine ⟨3060522878583896848651369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080697171445195798201825 3060522878583896848651369)
                      ·
                        rfl

theorem cell23_5960347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3, 2].length) (baseStart_5960347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960347 prefixEnd_5960347 := by exact prefixLift 5960347
  have htrace : WordTrace (prefixWord ++ tailWord_5960347) baseStart_5960347 baseEnd_5960347 := by
    simpa [prefixWord, tailWord_5960347, baseEnd_5960347] using wordTrace_append hprefix tailTrace_5960347
  have hstable : (prefixWord ++ tailWord_5960347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960347).length < 2 ^ (prefixWord ++ tailWord_5960347).sum := by decide
  have hdescent : baseEnd_5960347 < baseStart_5960347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960377 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 8, 2]
def baseStart_5960377 : Nat := 118140960795 + 5960377 * 2 ^ 59
def prefixEnd_5960377 : Nat := 4983230072969 + 3 ^ 40 * 5960377 * 2
def baseEnd_5960377 : Nat := 3060538283003531731276231

theorem tailTrace_5960377 : CollatzResearch.WordTrace tailWord_5960377 prefixEnd_5960377 3060538283003531731276231 := by
  unfold tailWord_5960377
  simp only [CollatzResearch.WordTrace]
  refine ⟨217392808727579555193463385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144928539151719703462308923 217392808727579555193463385)
  ·
    refine ⟨163044606545684666395097539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217392808727579555193463385 163044606545684666395097539)
    ·
      refine ⟨244566909818526999592646309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163044606545684666395097539 244566909818526999592646309)
      ·
        refine ⟨45856295590973812423621183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244566909818526999592646309 45856295590973812423621183)
        ·
          refine ⟨68784443386460718635431775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45856295590973812423621183 68784443386460718635431775)
          ·
            refine ⟨103176665079691077953147663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68784443386460718635431775 103176665079691077953147663)
            ·
              refine ⟨154764997619536616929721495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103176665079691077953147663 154764997619536616929721495)
              ·
                refine ⟨232147496429304925394582243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154764997619536616929721495 232147496429304925394582243)
                ·
                  refine ⟨348221244643957388091873365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232147496429304925394582243 348221244643957388091873365)
                  ·
                    refine ⟨4080717710671375641701641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 348221244643957388091873365 4080717710671375641701641)
                    ·
                      refine ⟨3060538283003531731276231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080717710671375641701641 3060538283003531731276231)
                      ·
                        rfl

theorem cell23_5960377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_5960377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960377 prefixEnd_5960377 := by exact prefixLift 5960377
  have htrace : WordTrace (prefixWord ++ tailWord_5960377) baseStart_5960377 baseEnd_5960377 := by
    simpa [prefixWord, tailWord_5960377, baseEnd_5960377] using wordTrace_append hprefix tailTrace_5960377
  have hstable : (prefixWord ++ tailWord_5960377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960377).length < 2 ^ (prefixWord ++ tailWord_5960377).sum := by decide
  have hdescent : baseEnd_5960377 < baseStart_5960377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960388 : List Nat := [2, 3, 3, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_5960388 : Nat := 118140960795 + 5960388 * 2 ^ 59
def prefixEnd_5960388 : Nat := 4983230072969 + 3 ^ 40 * 5960388 * 2
def baseEnd_5960388 : Nat := 3060543931290731188238681

theorem tailTrace_5960388 : CollatzResearch.WordTrace tailWord_5960388 prefixEnd_5960388 3060543931290731188238681 := by
  unfold tailWord_5960388
  simp only [CollatzResearch.WordTrace]
  refine ⟨108696604965269852036056909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144928806620359802714742545 108696604965269852036056909)
  ·
    refine ⟨40761226861976194513521341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108696604965269852036056909 40761226861976194513521341)
    ·
      refine ⟨15285460073241072942570503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40761226861976194513521341 15285460073241072942570503)
      ·
        refine ⟨22928190109861609413855755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15285460073241072942570503 22928190109861609413855755)
        ·
          refine ⟨34392285164792414120783633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22928190109861609413855755 34392285164792414120783633)
          ·
            refine ⟨25794213873594310590587725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34392285164792414120783633 25794213873594310590587725)
            ·
              refine ⟨9672830202597866471470397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25794213873594310590587725 9672830202597866471470397)
              ·
                refine ⟨3627311325974199926801399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9672830202597866471470397 3627311325974199926801399)
                ·
                  refine ⟨5440966988961299890202099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627311325974199926801399 5440966988961299890202099)
                  ·
                    refine ⟨8161450483441949835303149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5440966988961299890202099 8161450483441949835303149)
                    ·
                      refine ⟨3060543931290731188238681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161450483441949835303149 3060543931290731188238681)
                      ·
                        rfl

theorem cell23_5960388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_5960388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960388 prefixEnd_5960388 := by exact prefixLift 5960388
  have htrace : WordTrace (prefixWord ++ tailWord_5960388) baseStart_5960388 baseEnd_5960388 := by
    simpa [prefixWord, tailWord_5960388, baseEnd_5960388] using wordTrace_append hprefix tailTrace_5960388
  have hstable : (prefixWord ++ tailWord_5960388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960388).length < 2 ^ (prefixWord ++ tailWord_5960388).sum := by decide
  have hdescent : baseEnd_5960388 < baseStart_5960388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960394 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_5960394 : Nat := 118140960795 + 5960394 * 2 ^ 59
def prefixEnd_5960394 : Nat := 4983230072969 + 3 ^ 40 * 5960394 * 2
def baseEnd_5960394 : Nat := 3060547012174658164763653

theorem tailTrace_5960394 : CollatzResearch.WordTrace tailWord_5960394 prefixEnd_5960394 3060547012174658164763653 := by
  unfold tailWord_5960394
  simp only [CollatzResearch.WordTrace]
  refine ⟨54348357192129491774208059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144928952512345311397888157 54348357192129491774208059)
  ·
    refine ⟨81522535788194237661312089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54348357192129491774208059 81522535788194237661312089)
    ·
      refine ⟨61141901841145678245984067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81522535788194237661312089 61141901841145678245984067)
      ·
        refine ⟨91712852761718517368976101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61141901841145678245984067 91712852761718517368976101)
        ·
          refine ⟨17196159892822222006683019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91712852761718517368976101 17196159892822222006683019)
          ·
            refine ⟨25794239839233333010024529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17196159892822222006683019 25794239839233333010024529)
            ·
              refine ⟨19345679879424999757518397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25794239839233333010024529 19345679879424999757518397)
              ·
                refine ⟨7254629954784374909069399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19345679879424999757518397 7254629954784374909069399)
                ·
                  refine ⟨10881944932176562363604099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7254629954784374909069399 10881944932176562363604099)
                  ·
                    refine ⟨16322917398264843545406149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10881944932176562363604099 16322917398264843545406149)
                    ·
                      refine ⟨3060547012174658164763653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16322917398264843545406149 3060547012174658164763653)
                      ·
                        rfl

theorem cell23_5960394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_5960394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960394 prefixEnd_5960394 := by exact prefixLift 5960394
  have htrace : WordTrace (prefixWord ++ tailWord_5960394) baseStart_5960394 baseEnd_5960394 := by
    simpa [prefixWord, tailWord_5960394, baseEnd_5960394] using wordTrace_append hprefix tailTrace_5960394
  have hstable : (prefixWord ++ tailWord_5960394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960394).length < 2 ^ (prefixWord ++ tailWord_5960394).sum := by decide
  have hdescent : baseEnd_5960394 < baseStart_5960394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960405 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5960405 : Nat := 118140960795 + 5960405 * 2 ^ 59
def prefixEnd_5960405 : Nat := 4983230072969 + 3 ^ 40 * 5960405 * 2
def baseEnd_5960405 : Nat := 3060552660461857621726103

theorem tailTrace_5960405 : CollatzResearch.WordTrace tailWord_5960405 prefixEnd_5960405 3060552660461857621726103 := by
  unfold tailWord_5960405
  simp only [CollatzResearch.WordTrace]
  refine ⟨217393829971478115975482669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144929219980985410650321779 217393829971478115975482669)
  ·
    refine ⟨81522686239304293490806001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217393829971478115975482669 81522686239304293490806001)
    ·
      refine ⟨61142014679478220118104501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81522686239304293490806001 61142014679478220118104501)
      ·
        refine ⟨5732063876201083136072297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61142014679478220118104501 5732063876201083136072297)
        ·
          refine ⟨4299047907150812352054223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5732063876201083136072297 4299047907150812352054223)
          ·
            refine ⟨6448571860726218528081335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299047907150812352054223 6448571860726218528081335)
            ·
              refine ⟨9672857791089327792122003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448571860726218528081335 9672857791089327792122003)
              ·
                refine ⟨14509286686633991688183005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9672857791089327792122003 14509286686633991688183005)
                ·
                  refine ⟨5440982507487746883068627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14509286686633991688183005 5440982507487746883068627)
                  ·
                    refine ⟨8161473761231620324602941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5440982507487746883068627 8161473761231620324602941)
                    ·
                      refine ⟨3060552660461857621726103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161473761231620324602941 3060552660461857621726103)
                      ·
                        rfl

theorem cell23_5960405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5960405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960405 prefixEnd_5960405 := by exact prefixLift 5960405
  have htrace : WordTrace (prefixWord ++ tailWord_5960405) baseStart_5960405 baseEnd_5960405 := by
    simpa [prefixWord, tailWord_5960405, baseEnd_5960405] using wordTrace_append hprefix tailTrace_5960405
  have hstable : (prefixWord ++ tailWord_5960405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960405).length < 2 ^ (prefixWord ++ tailWord_5960405).sum := by decide
  have hdescent : baseEnd_5960405 < baseStart_5960405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960417 : List Nat := [1, 2, 3, 1, 4, 2, 2, 8]
def baseStart_5960417 : Nat := 118140960795 + 5960417 * 2 ^ 59
def prefixEnd_5960417 : Nat := 4983230072969 + 3 ^ 40 * 5960417 * 2
def baseEnd_5960417 : Nat := 113354030452952280547261

theorem tailTrace_5960417 : CollatzResearch.WordTrace tailWord_5960417 prefixEnd_5960417 113354030452952280547261 := by
  unfold tailWord_5960417
  simp only [CollatzResearch.WordTrace]
  refine ⟨217394267647434642024919505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144929511764956428016613003 217394267647434642024919505)
  ·
    refine ⟨163045700735575981518689629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217394267647434642024919505 163045700735575981518689629)
    ·
      refine ⟨61142137775840993069508611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163045700735575981518689629 61142137775840993069508611)
      ·
        refine ⟨91713206663761489604262917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61142137775840993069508611 91713206663761489604262917)
        ·
          refine ⟨17196226249455279300799297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91713206663761489604262917 17196226249455279300799297)
          ·
            refine ⟨12897169687091459475599473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17196226249455279300799297 12897169687091459475599473)
            ·
              refine ⟨9672877265318594606699605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12897169687091459475599473 9672877265318594606699605)
              ·
                refine ⟨113354030452952280547261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9672877265318594606699605 113354030452952280547261)
                ·
                  rfl

theorem cell23_5960417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 8].length) (baseStart_5960417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960417 prefixEnd_5960417 := by exact prefixLift 5960417
  have htrace : WordTrace (prefixWord ++ tailWord_5960417) baseStart_5960417 baseEnd_5960417 := by
    simpa [prefixWord, tailWord_5960417, baseEnd_5960417] using wordTrace_append hprefix tailTrace_5960417
  have hstable : (prefixWord ++ tailWord_5960417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960417).length < 2 ^ (prefixWord ++ tailWord_5960417).sum := by decide
  have hdescent : baseEnd_5960417 < baseStart_5960417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960421 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_5960421 : Nat := 118140960795 + 5960421 * 2 ^ 59
def prefixEnd_5960421 : Nat := 4983230072969 + 3 ^ 40 * 5960421 * 2
def baseEnd_5960421 : Nat := 1020186958717443186375343

theorem tailTrace_5960421 : CollatzResearch.WordTrace tailWord_5960421 prefixEnd_5960421 1020186958717443186375343 := by
  unfold tailWord_5960421
  simp only [CollatzResearch.WordTrace]
  refine ⟨217394413539420150708065117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144929609026280100472043411 217394413539420150708065117)
  ·
    refine ⟨81522905077282556515524419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217394413539420150708065117 81522905077282556515524419)
    ·
      refine ⟨122284357615923834773286629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81522905077282556515524419 122284357615923834773286629)
      ·
        refine ⟨22928317052985719019991243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122284357615923834773286629 22928317052985719019991243)
        ·
          refine ⟨34392475579478578529986865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22928317052985719019991243 34392475579478578529986865)
          ·
            refine ⟨25794356684608933897490149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34392475579478578529986865 25794356684608933897490149)
            ·
              refine ⟨4836441878364175105779403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25794356684608933897490149 4836441878364175105779403)
              ·
                refine ⟨7254662817546262658669105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836441878364175105779403 7254662817546262658669105)
                ·
                  refine ⟨5440997113159696994001829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7254662817546262658669105 5440997113159696994001829)
                  ·
                    refine ⟨1020186958717443186375343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5440997113159696994001829 1020186958717443186375343)
                    ·
                      rfl

theorem cell23_5960421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_5960421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960421 prefixEnd_5960421 := by exact prefixLift 5960421
  have htrace : WordTrace (prefixWord ++ tailWord_5960421) baseStart_5960421 baseEnd_5960421 := by
    simpa [prefixWord, tailWord_5960421, baseEnd_5960421] using wordTrace_append hprefix tailTrace_5960421
  have hstable : (prefixWord ++ tailWord_5960421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960421).length < 2 ^ (prefixWord ++ tailWord_5960421).sum := by decide
  have hdescent : baseEnd_5960421 < baseStart_5960421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960427 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 3]
def baseStart_5960427 : Nat := 118140960795 + 5960427 * 2 ^ 59
def prefixEnd_5960427 : Nat := 4983230072969 + 3 ^ 40 * 5960427 * 2
def baseEnd_5960427 : Nat := 3060563957036256535651001

theorem tailTrace_5960427 : CollatzResearch.WordTrace tailWord_5960427 prefixEnd_5960427 3060563957036256535651001 := by
  unfold tailWord_5960427
  simp only [CollatzResearch.WordTrace]
  refine ⟨217394632377398413732783535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144929754918265609155189023 217394632377398413732783535)
  ·
    refine ⟨326091948566097620599175303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217394632377398413732783535 326091948566097620599175303)
    ·
      refine ⟨489137922849146430898762955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326091948566097620599175303 489137922849146430898762955)
      ·
        refine ⟨733706884273719646348144433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489137922849146430898762955 733706884273719646348144433)
        ·
          refine ⟨550280163205289734761108325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733706884273719646348144433 550280163205289734761108325)
          ·
            refine ⟨103177530600991825267707811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 550280163205289734761108325 103177530600991825267707811)
            ·
              refine ⟨154766295901487737901561717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103177530600991825267707811 154766295901487737901561717)
              ·
                refine ⟨14509340240764475428271411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154766295901487737901561717 14509340240764475428271411)
                ·
                  refine ⟨21764010361146713142407117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14509340240764475428271411 21764010361146713142407117)
                  ·
                    refine ⟨8161503885430017428402669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21764010361146713142407117 8161503885430017428402669)
                    ·
                      refine ⟨3060563957036256535651001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161503885430017428402669 3060563957036256535651001)
                      ·
                        rfl

theorem cell23_5960427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 3].length) (baseStart_5960427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960427 prefixEnd_5960427 := by exact prefixLift 5960427
  have htrace : WordTrace (prefixWord ++ tailWord_5960427) baseStart_5960427 baseEnd_5960427 := by
    simpa [prefixWord, tailWord_5960427, baseEnd_5960427] using wordTrace_append hprefix tailTrace_5960427
  have hstable : (prefixWord ++ tailWord_5960427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960427).length < 2 ^ (prefixWord ++ tailWord_5960427).sum := by decide
  have hdescent : baseEnd_5960427 < baseStart_5960427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960431 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 3]
def baseStart_5960431 : Nat := 118140960795 + 5960431 * 2 ^ 59
def prefixEnd_5960431 : Nat := 4983230072969 + 3 ^ 40 * 5960431 * 2
def baseEnd_5960431 : Nat := 3060566010958874520000983

theorem tailTrace_5960431 : CollatzResearch.WordTrace tailWord_5960431 prefixEnd_5960431 3060566010958874520000983 := by
  unfold tailWord_5960431
  simp only [CollatzResearch.WordTrace]
  refine ⟨217394778269383922415929147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144929852179589281610619431 217394778269383922415929147)
  ·
    refine ⟨326092167404075883623893721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217394778269383922415929147 326092167404075883623893721)
    ·
      refine ⟨244569125553056912717920291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326092167404075883623893721 244569125553056912717920291)
      ·
        refine ⟨366853688329585369076880437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244569125553056912717920291 366853688329585369076880437)
        ·
          refine ⟨34392533280898628350957541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 366853688329585369076880437 34392533280898628350957541)
          ·
            refine ⟨6448599990168492815804539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34392533280898628350957541 6448599990168492815804539)
            ·
              refine ⟨9672899985252739223706809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6448599990168492815804539 9672899985252739223706809)
              ·
                refine ⟨7254674988939554417780107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9672899985252739223706809 7254674988939554417780107)
                ·
                  refine ⟨10882012483409331626670161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7254674988939554417780107 10882012483409331626670161)
                  ·
                    refine ⟨8161509362556998720002621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10882012483409331626670161 8161509362556998720002621)
                    ·
                      refine ⟨3060566010958874520000983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161509362556998720002621 3060566010958874520000983)
                      ·
                        rfl

theorem cell23_5960431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_5960431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960431 prefixEnd_5960431 := by exact prefixLift 5960431
  have htrace : WordTrace (prefixWord ++ tailWord_5960431) baseStart_5960431 baseEnd_5960431 := by
    simpa [prefixWord, tailWord_5960431, baseEnd_5960431] using wordTrace_append hprefix tailTrace_5960431
  have hstable : (prefixWord ++ tailWord_5960431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960431).length < 2 ^ (prefixWord ++ tailWord_5960431).sum := by decide
  have hdescent : baseEnd_5960431 < baseStart_5960431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960444 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_5960444 : Nat := 118140960795 + 5960444 * 2 ^ 59
def prefixEnd_5960444 : Nat := 4983230072969 + 3 ^ 40 * 5960444 * 2
def baseEnd_5960444 : Nat := 3060572686207382969138423

theorem tailTrace_5960444 : CollatzResearch.WordTrace tailWord_5960444 prefixEnd_5960444 3060572686207382969138423 := by
  unfold tailWord_5960444
  simp only [CollatzResearch.WordTrace]
  refine ⟨108697626209168412818076193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144930168278891217090768257 108697626209168412818076193)
  ·
    refine ⟨81523219656876309613557145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108697626209168412818076193 81523219656876309613557145)
    ·
      refine ⟨61142414742657232210167859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81523219656876309613557145 61142414742657232210167859)
      ·
        refine ⟨91713622113985848315251789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61142414742657232210167859 91713622113985848315251789)
        ·
          refine ⟨34392608292744693118219421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91713622113985848315251789 34392608292744693118219421)
          ·
            refine ⟨12897228109779259919332283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34392608292744693118219421 12897228109779259919332283)
            ·
              refine ⟨19345842164668889878998425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12897228109779259919332283 19345842164668889878998425)
              ·
                refine ⟨14509381623501667409248819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19345842164668889878998425 14509381623501667409248819)
                ·
                  refine ⟨21764072435252501113873229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14509381623501667409248819 21764072435252501113873229)
                  ·
                    refine ⟨8161527163219687917702461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21764072435252501113873229 8161527163219687917702461)
                    ·
                      refine ⟨3060572686207382969138423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161527163219687917702461 3060572686207382969138423)
                      ·
                        rfl

theorem cell23_5960444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_5960444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960444 prefixEnd_5960444 := by exact prefixLift 5960444
  have htrace : WordTrace (prefixWord ++ tailWord_5960444) baseStart_5960444 baseEnd_5960444 := by
    simpa [prefixWord, tailWord_5960444, baseEnd_5960444] using wordTrace_append hprefix tailTrace_5960444
  have hstable : (prefixWord ++ tailWord_5960444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960444).length < 2 ^ (prefixWord ++ tailWord_5960444).sum := by decide
  have hdescent : baseEnd_5960444 < baseStart_5960444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960497 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_5960497 : Nat := 118140960795 + 5960497 * 2 ^ 59
def prefixEnd_5960497 : Nat := 4983230072969 + 3 ^ 40 * 5960497 * 2
def baseEnd_5960497 : Nat := 3060599900682071261775679

theorem tailTrace_5960497 : CollatzResearch.WordTrace tailWord_5960497 prefixEnd_5960497 3060599900682071261775679 := by
  unfold tailWord_5960497
  simp only [CollatzResearch.WordTrace]
  refine ⟨217397185487144815687831745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144931456991429877125221163 217397185487144815687831745)
  ·
    refine ⟨163047889115358611765873809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217397185487144815687831745 163047889115358611765873809)
    ·
      refine ⟨122285916836518958824405357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163047889115358611765873809 122285916836518958824405357)
      ·
        refine ⟨45857218813694609559152009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122285916836518958824405357 45857218813694609559152009)
        ·
          refine ⟨34392914110270957169364007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45857218813694609559152009 34392914110270957169364007)
          ·
            refine ⟨51589371165406435754046011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34392914110270957169364007 51589371165406435754046011)
            ·
              refine ⟨77384056748109653631069017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51589371165406435754046011 77384056748109653631069017)
              ·
                refine ⟨58038042561082240223301763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77384056748109653631069017 58038042561082240223301763)
                ·
                  refine ⟨87057063841623360334952645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58038042561082240223301763 87057063841623360334952645)
                  ·
                    refine ⟨16323199470304380062803621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87057063841623360334952645 16323199470304380062803621)
                    ·
                      refine ⟨3060599900682071261775679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16323199470304380062803621 3060599900682071261775679)
                      ·
                        rfl

theorem cell23_5960497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_5960497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960497 prefixEnd_5960497 := by exact prefixLift 5960497
  have htrace : WordTrace (prefixWord ++ tailWord_5960497) baseStart_5960497 baseEnd_5960497 := by
    simpa [prefixWord, tailWord_5960497, baseEnd_5960497] using wordTrace_append hprefix tailTrace_5960497
  have hstable : (prefixWord ++ tailWord_5960497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960497).length < 2 ^ (prefixWord ++ tailWord_5960497).sum := by decide
  have hdescent : baseEnd_5960497 < baseStart_5960497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960501 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_5960501 : Nat := 118140960795 + 5960501 * 2 ^ 59
def prefixEnd_5960501 : Nat := 4983230072969 + 3 ^ 40 * 5960501 * 2
def baseEnd_5960501 : Nat := 3060601954604689246125661

theorem tailTrace_5960501 : CollatzResearch.WordTrace tailWord_5960501 prefixEnd_5960501 3060601954604689246125661 := by
  unfold tailWord_5960501
  simp only [CollatzResearch.WordTrace]
  refine ⟨217397331379130324370977357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144931554252753549580651571 217397331379130324370977357)
  ·
    refine ⟨81523999267173871639116509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217397331379130324370977357 81523999267173871639116509)
    ·
      refine ⟨30571499725190201864668691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81523999267173871639116509 30571499725190201864668691)
      ·
        refine ⟨45857249587785302797003037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30571499725190201864668691 45857249587785302797003037)
        ·
          refine ⟨17196468595419488548876139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45857249587785302797003037 17196468595419488548876139)
          ·
            refine ⟨25794702893129232823314209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17196468595419488548876139 25794702893129232823314209)
            ·
              refine ⟨19346027169846924617485657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25794702893129232823314209 19346027169846924617485657)
              ·
                refine ⟨14509520377385193463114243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19346027169846924617485657 14509520377385193463114243)
                ·
                  refine ⟨21764280566077790194671365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14509520377385193463114243 21764280566077790194671365)
                  ·
                    refine ⟨4080802606139585661500881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21764280566077790194671365 4080802606139585661500881)
                    ·
                      refine ⟨3060601954604689246125661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080802606139585661500881 3060601954604689246125661)
                      ·
                        rfl

theorem cell23_5960501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_5960501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960501 prefixEnd_5960501 := by exact prefixLift 5960501
  have htrace : WordTrace (prefixWord ++ tailWord_5960501) baseStart_5960501 baseEnd_5960501 := by
    simpa [prefixWord, tailWord_5960501, baseEnd_5960501] using wordTrace_append hprefix tailTrace_5960501
  have hstable : (prefixWord ++ tailWord_5960501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960501).length < 2 ^ (prefixWord ++ tailWord_5960501).sum := by decide
  have hdescent : baseEnd_5960501 < baseStart_5960501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960524 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 7]
def baseStart_5960524 : Nat := 118140960795 + 5960524 * 2 ^ 59
def prefixEnd_5960524 : Nat := 4983230072969 + 3 ^ 40 * 5960524 * 2
def baseEnd_5960524 : Nat := 340068196073304739570895

theorem tailTrace_5960524 : CollatzResearch.WordTrace tailWord_5960524 prefixEnd_5960524 340068196073304739570895 := by
  unfold tailWord_5960524
  simp only [CollatzResearch.WordTrace]
  refine ⟨108699085129023499649532313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144932113505364666199376417 108699085129023499649532313)
  ·
    refine ⟨81524313846767624737149235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108699085129023499649532313 81524313846767624737149235)
    ·
      refine ⟨122286470770151437105723853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81524313846767624737149235 122286470770151437105723853)
      ·
        refine ⟨45857426538806788914646445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122286470770151437105723853 45857426538806788914646445)
        ·
          refine ⟨17196534952052545842992417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45857426538806788914646445 17196534952052545842992417)
          ·
            refine ⟨12897401214039409382244313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17196534952052545842992417 12897401214039409382244313)
            ·
              refine ⟨9673050910529557036683235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12897401214039409382244313 9673050910529557036683235)
              ·
                refine ⟨14509576365794335555024853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9673050910529557036683235 14509576365794335555024853)
                ·
                  refine ⟨340068196073304739570895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14509576365794335555024853 340068196073304739570895)
                  ·
                    rfl

theorem cell23_5960524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_5960524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960524 prefixEnd_5960524 := by exact prefixLift 5960524
  have htrace : WordTrace (prefixWord ++ tailWord_5960524) baseStart_5960524 baseEnd_5960524 := by
    simpa [prefixWord, tailWord_5960524, baseEnd_5960524] using wordTrace_append hprefix tailTrace_5960524
  have hstable : (prefixWord ++ tailWord_5960524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960524).length < 2 ^ (prefixWord ++ tailWord_5960524).sum := by decide
  have hdescent : baseEnd_5960524 < baseStart_5960524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960535 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 2, 2, 2]
def baseStart_5960535 : Nat := 118140960795 + 5960535 * 2 ^ 59
def prefixEnd_5960535 : Nat := 4983230072969 + 3 ^ 40 * 5960535 * 2
def baseEnd_5960535 : Nat := 3060619412946942113100505

theorem tailTrace_5960535 : CollatzResearch.WordTrace tailWord_5960535 prefixEnd_5960535 3060619412946942113100505 := by
  unfold tailWord_5960535
  simp only [CollatzResearch.WordTrace]
  refine ⟨217398571461007148177715059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144932380974004765451810039 217398571461007148177715059)
  ·
    refine ⟨326097857191510722266572589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217398571461007148177715059 326097857191510722266572589)
    ·
      refine ⟨122286696446816520849964721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326097857191510722266572589 122286696446816520849964721)
      ·
        refine ⟨91715022335112390637473541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122286696446816520849964721 91715022335112390637473541)
        ·
          refine ⟨17196566687833573244526289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91715022335112390637473541 17196566687833573244526289)
          ·
            refine ⟨12897425015875179933394717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17196566687833573244526289 12897425015875179933394717)
            ·
              refine ⟨4836534380953192475023019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12897425015875179933394717 4836534380953192475023019)
              ·
                refine ⟨7254801571429788712534529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836534380953192475023019 7254801571429788712534529)
                ·
                  refine ⟨5441101178572341534400897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7254801571429788712534529 5441101178572341534400897)
                  ·
                    refine ⟨4080825883929256150800673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5441101178572341534400897 4080825883929256150800673)
                    ·
                      refine ⟨3060619412946942113100505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080825883929256150800673 3060619412946942113100505)
                      ·
                        rfl

theorem cell23_5960535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_5960535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960535 prefixEnd_5960535 := by exact prefixLift 5960535
  have htrace : WordTrace (prefixWord ++ tailWord_5960535) baseStart_5960535 baseEnd_5960535 := by
    simpa [prefixWord, tailWord_5960535, baseEnd_5960535] using wordTrace_append hprefix tailTrace_5960535
  have hstable : (prefixWord ++ tailWord_5960535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960535).length < 2 ^ (prefixWord ++ tailWord_5960535).sum := by decide
  have hdescent : baseEnd_5960535 < baseStart_5960535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960537 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 1, 7]
def baseStart_5960537 : Nat := 118140960795 + 5960537 * 2 ^ 59
def prefixEnd_5960537 : Nat := 4983230072969 + 3 ^ 40 * 5960537 * 2
def baseEnd_5960537 : Nat := 1020206813302750368425165

theorem tailTrace_5960537 : CollatzResearch.WordTrace tailWord_5960537 prefixEnd_5960537 1020206813302750368425165 := by
  unfold tailWord_5960537
  simp only [CollatzResearch.WordTrace]
  refine ⟨217398644406999902519287865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144932429604666601679525243 217398644406999902519287865)
  ·
    refine ⟨163048983305249926889465899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217398644406999902519287865 163048983305249926889465899)
    ·
      refine ⟨244573474957874890334198849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163048983305249926889465899 244573474957874890334198849)
      ·
        refine ⟨183430106218406167750649137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244573474957874890334198849 183430106218406167750649137)
        ·
          refine ⟨137572579663804625812986853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183430106218406167750649137 137572579663804625812986853)
          ·
            refine ⟨25794858686963367339935035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137572579663804625812986853 25794858686963367339935035)
            ·
              refine ⟨38692288030445051009902553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25794858686963367339935035 38692288030445051009902553)
              ·
                refine ⟨29019216022833788257426915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38692288030445051009902553 29019216022833788257426915)
                ·
                  refine ⟨43528824034250682386140373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29019216022833788257426915 43528824034250682386140373)
                  ·
                    refine ⟨1020206813302750368425165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43528824034250682386140373 1020206813302750368425165)
                    ·
                      rfl

theorem cell23_5960537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_5960537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960537 prefixEnd_5960537 := by exact prefixLift 5960537
  have htrace : WordTrace (prefixWord ++ tailWord_5960537) baseStart_5960537 baseEnd_5960537 := by
    simpa [prefixWord, tailWord_5960537, baseEnd_5960537] using wordTrace_append hprefix tailTrace_5960537
  have hstable : (prefixWord ++ tailWord_5960537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960537).length < 2 ^ (prefixWord ++ tailWord_5960537).sum := by decide
  have hdescent : baseEnd_5960537 < baseStart_5960537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960587 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6]
def baseStart_5960587 : Nat := 118140960795 + 5960587 * 2 ^ 59
def prefixEnd_5960587 : Nat := 4983230072969 + 3 ^ 40 * 5960587 * 2
def baseEnd_5960587 : Nat := 3060646113940975909650265

theorem tailTrace_5960587 : CollatzResearch.WordTrace tailWord_5960587 prefixEnd_5960587 3060646113940975909650265 := by
  unfold tailWord_5960587
  simp only [CollatzResearch.WordTrace]
  refine ⟨217400468056818761058608015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144933645371212507372405343 217400468056818761058608015)
  ·
    refine ⟨326100702085228141587912023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217400468056818761058608015 326100702085228141587912023)
    ·
      refine ⟨489151053127842212381868035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326100702085228141587912023 489151053127842212381868035)
      ·
        refine ⟨733726579691763318572802053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489151053127842212381868035 733726579691763318572802053)
        ·
          refine ⟨137573733692205622232400385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 733726579691763318572802053 137573733692205622232400385)
          ·
            refine ⟨103180300269154216674300289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137573733692205622232400385 103180300269154216674300289)
            ·
              refine ⟨77385225201865662505725217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103180300269154216674300289 77385225201865662505725217)
              ·
                refine ⟨58038918901399246879293913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77385225201865662505725217 58038918901399246879293913)
                ·
                  refine ⟨43529189176049435159470435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58038918901399246879293913 43529189176049435159470435)
                  ·
                    refine ⟨65293783764074152739205653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43529189176049435159470435 65293783764074152739205653)
                    ·
                      refine ⟨3060646113940975909650265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65293783764074152739205653 3060646113940975909650265)
                      ·
                        rfl

theorem cell23_5960587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_5960587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960587 prefixEnd_5960587 := by exact prefixLift 5960587
  have htrace : WordTrace (prefixWord ++ tailWord_5960587) baseStart_5960587 baseEnd_5960587 := by
    simpa [prefixWord, tailWord_5960587, baseEnd_5960587] using wordTrace_append hprefix tailTrace_5960587
  have hstable : (prefixWord ++ tailWord_5960587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960587).length < 2 ^ (prefixWord ++ tailWord_5960587).sum := by decide
  have hdescent : baseEnd_5960587 < baseStart_5960587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960658 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_5960658 : Nat := 118140960795 + 5960658 * 2 ^ 59
def prefixEnd_5960658 : Nat := 4983230072969 + 3 ^ 40 * 5960658 * 2
def baseEnd_5960658 : Nat := 3060682571067445131862439

theorem tailTrace_5960658 : CollatzResearch.WordTrace tailWord_5960658 prefixEnd_5960658 3060682571067445131862439 := by
  unfold tailWord_5960658
  simp only [CollatzResearch.WordTrace]
  refine ⟨54350764409890385046110657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144935371759707693456295085 54350764409890385046110657)
  ·
    refine ⟨40763073307417788784582993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54350764409890385046110657 40763073307417788784582993)
    ·
      refine ⟨30572304980563341588437245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40763073307417788784582993 30572304980563341588437245)
      ·
        refine ⟨11464614367711253095663967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30572304980563341588437245 11464614367711253095663967)
        ·
          refine ⟨17196921551566879643495951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11464614367711253095663967 17196921551566879643495951)
          ·
            refine ⟨25795382327350319465243927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17196921551566879643495951 25795382327350319465243927)
            ·
              refine ⟨38693073491025479197865891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25795382327350319465243927 38693073491025479197865891)
              ·
                refine ⟨58039610236538218796798837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38693073491025479197865891 58039610236538218796798837)
                ·
                  refine ⟨5441213459675458012199891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58039610236538218796798837 5441213459675458012199891)
                  ·
                    refine ⟨8161820189513187018299837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5441213459675458012199891 8161820189513187018299837)
                    ·
                      refine ⟨3060682571067445131862439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161820189513187018299837 3060682571067445131862439)
                      ·
                        rfl

theorem cell23_5960658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_5960658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960658 prefixEnd_5960658 := by exact prefixLift 5960658
  have htrace : WordTrace (prefixWord ++ tailWord_5960658) baseStart_5960658 baseEnd_5960658 := by
    simpa [prefixWord, tailWord_5960658, baseEnd_5960658] using wordTrace_append hprefix tailTrace_5960658
  have hstable : (prefixWord ++ tailWord_5960658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960658).length < 2 ^ (prefixWord ++ tailWord_5960658).sum := by decide
  have hdescent : baseEnd_5960658 < baseStart_5960658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960675 : List Nat := [1, 1, 1, 6, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5960675 : Nat := 118140960795 + 5960675 * 2 ^ 59
def prefixEnd_5960675 : Nat := 4983230072969 + 3 ^ 40 * 5960675 * 2
def baseEnd_5960675 : Nat := 3060691300238571565349861

theorem tailTrace_5960675 : CollatzResearch.WordTrace tailWord_5960675 prefixEnd_5960675 3060691300238571565349861 := by
  unfold tailWord_5960675
  simp only [CollatzResearch.WordTrace]
  refine ⟨217403677680499952087811479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144935785120333301391874319 217403677680499952087811479)
  ·
    refine ⟨326105516520749928131717219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217403677680499952087811479 326105516520749928131717219)
    ·
      refine ⟨489158274781124892197575829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326105516520749928131717219 489158274781124892197575829)
      ·
        refine ⟨22929294130365229321761367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 489158274781124892197575829 22929294130365229321761367)
        ·
          refine ⟨34393941195547843982642051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22929294130365229321761367 34393941195547843982642051)
          ·
            refine ⟨51590911793321765973963077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34393941195547843982642051 51590911793321765973963077)
            ·
              refine ⟨9673295961247831120118077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51590911793321765973963077 9673295961247831120118077)
              ·
                refine ⟨3627485985467936670044279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9673295961247831120118077 3627485985467936670044279)
                ·
                  refine ⟨5441228978201905005066419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627485985467936670044279 5441228978201905005066419)
                  ·
                    refine ⟨8161843467302857507599629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5441228978201905005066419 8161843467302857507599629)
                    ·
                      refine ⟨3060691300238571565349861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161843467302857507599629 3060691300238571565349861)
                      ·
                        rfl

theorem cell23_5960675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5960675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960675 prefixEnd_5960675 := by exact prefixLift 5960675
  have htrace : WordTrace (prefixWord ++ tailWord_5960675) baseStart_5960675 baseEnd_5960675 := by
    simpa [prefixWord, tailWord_5960675, baseEnd_5960675] using wordTrace_append hprefix tailTrace_5960675
  have hstable : (prefixWord ++ tailWord_5960675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960675).length < 2 ^ (prefixWord ++ tailWord_5960675).sum := by decide
  have hdescent : baseEnd_5960675 < baseStart_5960675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960718 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_5960718 : Nat := 118140960795 + 5960718 * 2 ^ 59
def prefixEnd_5960718 : Nat := 4983230072969 + 3 ^ 40 * 5960718 * 2
def baseEnd_5960718 : Nat := 3060713379906714897112163

theorem tailTrace_5960718 : CollatzResearch.WordTrace tailWord_5960718 prefixEnd_5960718 3060713379906714897112163 := by
  unfold tailWord_5960718
  simp only [CollatzResearch.WordTrace]
  refine ⟨27175655752418021303953351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144936830679562780287751205 27175655752418021303953351)
  ·
    refine ⟨40763483628627031955930027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27175655752418021303953351 40763483628627031955930027)
    ·
      refine ⟨61145225442940547933895041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40763483628627031955930027 61145225442940547933895041)
      ·
        refine ⟨45858919082205410950421281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61145225442940547933895041 45858919082205410950421281)
        ·
          refine ⟨34394189311654058212815961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45858919082205410950421281 34394189311654058212815961)
          ·
            refine ⟨25795641983740543659611971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34394189311654058212815961 25795641983740543659611971)
            ·
              refine ⟨38693462975610815489417957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25795641983740543659611971 38693462975610815489417957)
              ·
                refine ⟨7255024307927027904265867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38693462975610815489417957 7255024307927027904265867)
                ·
                  refine ⟨10882536461890541856398801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7255024307927027904265867 10882536461890541856398801)
                  ·
                    refine ⟨8161902346417906392299101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10882536461890541856398801 8161902346417906392299101)
                    ·
                      refine ⟨3060713379906714897112163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161902346417906392299101 3060713379906714897112163)
                      ·
                        rfl

theorem cell23_5960718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_5960718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960718 prefixEnd_5960718 := by exact prefixLift 5960718
  have htrace : WordTrace (prefixWord ++ tailWord_5960718) baseStart_5960718 baseEnd_5960718 := by
    simpa [prefixWord, tailWord_5960718, baseEnd_5960718] using wordTrace_append hprefix tailTrace_5960718
  have hstable : (prefixWord ++ tailWord_5960718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960718).length < 2 ^ (prefixWord ++ tailWord_5960718).sum := by decide
  have hdescent : baseEnd_5960718 < baseStart_5960718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960748 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_5960748 : Nat := 118140960795 + 5960748 * 2 ^ 59
def prefixEnd_5960748 : Nat := 4983230072969 + 3 ^ 40 * 5960748 * 2
def baseEnd_5960748 : Nat := 3060728784326349779737025

theorem tailTrace_5960748 : CollatzResearch.WordTrace tailWord_5960748 prefixEnd_5960748 3060728784326349779737025 := by
  unfold tailWord_5960748
  simp only [CollatzResearch.WordTrace]
  refine ⟨108703170104617742777609449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144937560139490323703479265 108703170104617742777609449)
  ·
    refine ⟨81527377578463307083207087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108703170104617742777609449 81527377578463307083207087)
    ·
      refine ⟨122291066367694960624810631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81527377578463307083207087 122291066367694960624810631)
      ·
        refine ⟨183436599551542440937215947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122291066367694960624810631 183436599551542440937215947)
        ·
          refine ⟨275154899327313661405823921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183436599551542440937215947 275154899327313661405823921)
          ·
            refine ⟨206366174495485246054367941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275154899327313661405823921 206366174495485246054367941)
            ·
              refine ⟨38693657717903483635193989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206366174495485246054367941 38693657717903483635193989)
              ·
                refine ⟨7255060822106903181598873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38693657717903483635193989 7255060822106903181598873)
                ·
                  refine ⟨5441295616580177386199155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255060822106903181598873 5441295616580177386199155)
                  ·
                    refine ⟨8161943424870266079298733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5441295616580177386199155 8161943424870266079298733)
                    ·
                      refine ⟨3060728784326349779737025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161943424870266079298733 3060728784326349779737025)
                      ·
                        rfl

theorem cell23_5960748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_5960748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960748 prefixEnd_5960748 := by exact prefixLift 5960748
  have htrace : WordTrace (prefixWord ++ tailWord_5960748) baseStart_5960748 baseEnd_5960748 := by
    simpa [prefixWord, tailWord_5960748, baseEnd_5960748] using wordTrace_append hprefix tailTrace_5960748
  have hstable : (prefixWord ++ tailWord_5960748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960748).length < 2 ^ (prefixWord ++ tailWord_5960748).sum := by decide
  have hdescent : baseEnd_5960748 < baseStart_5960748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960765 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_5960765 : Nat := 118140960795 + 5960765 * 2 ^ 59
def prefixEnd_5960765 : Nat := 4983230072969 + 3 ^ 40 * 5960765 * 2
def baseEnd_5960765 : Nat := 3060737513497476213224447

theorem tailTrace_5960765 : CollatzResearch.WordTrace tailWord_5960765 prefixEnd_5960765 3060737513497476213224447 := by
  unfold tailWord_5960765
  simp only [CollatzResearch.WordTrace]
  refine ⟨217406960250173897458587749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144937973500115931639058499 217406960250173897458587749)
  ·
    refine ⟨40763805046907605773485203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217406960250173897458587749 40763805046907605773485203)
    ·
      refine ⟨61145707570361408660227805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40763805046907605773485203 61145707570361408660227805)
      ·
        refine ⟨22929640338885528247585427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61145707570361408660227805 22929640338885528247585427)
        ·
          refine ⟨34394460508328292371378141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22929640338885528247585427 34394460508328292371378141)
          ·
            refine ⟨12897922690623109639266803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34394460508328292371378141 12897922690623109639266803)
            ·
              refine ⟨19346884035934664458900205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12897922690623109639266803 19346884035934664458900205)
              ·
                refine ⟨7255081513475499172087577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19346884035934664458900205 7255081513475499172087577)
                ·
                  refine ⟨5441311135106624379065683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255081513475499172087577 5441311135106624379065683)
                  ·
                    refine ⟨8161966702659936568598525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5441311135106624379065683 8161966702659936568598525)
                    ·
                      refine ⟨3060737513497476213224447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8161966702659936568598525 3060737513497476213224447)
                      ·
                        rfl

theorem cell23_5960765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_5960765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960765 prefixEnd_5960765 := by exact prefixLift 5960765
  have htrace : WordTrace (prefixWord ++ tailWord_5960765) baseStart_5960765 baseEnd_5960765 := by
    simpa [prefixWord, tailWord_5960765, baseEnd_5960765] using wordTrace_append hprefix tailTrace_5960765
  have hstable : (prefixWord ++ tailWord_5960765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960765).length < 2 ^ (prefixWord ++ tailWord_5960765).sum := by decide
  have hdescent : baseEnd_5960765 < baseStart_5960765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960775 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_5960775 : Nat := 118140960795 + 5960775 * 2 ^ 59
def prefixEnd_5960775 : Nat := 4983230072969 + 3 ^ 40 * 5960775 * 2
def baseEnd_5960775 : Nat := 3060742648304021174099401

theorem tailTrace_5960775 : CollatzResearch.WordTrace tailWord_5960775 prefixEnd_5960775 3060742648304021174099401 := by
  unfold tailWord_5960775
  simp only [CollatzResearch.WordTrace]
  refine ⟨217407324980137669166451779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144938216653425112777634519 217407324980137669166451779)
  ·
    refine ⟨326110987470206503749677669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217407324980137669166451779 326110987470206503749677669)
    ·
      refine ⟨61145810150663719453064563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326110987470206503749677669 61145810150663719453064563)
      ·
        refine ⟨91718715225995579179596845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61145810150663719453064563 91718715225995579179596845)
        ·
          refine ⟨34394518209748342192348817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91718715225995579179596845 34394518209748342192348817)
          ·
            refine ⟨25795888657311256644261613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34394518209748342192348817 25795888657311256644261613)
            ·
              refine ⟨9673458246491721241598105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25795888657311256644261613 9673458246491721241598105)
              ·
                refine ⟨7255093684868790931198579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9673458246491721241598105 7255093684868790931198579)
                ·
                  refine ⟨10882640527303186396797869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7255093684868790931198579 10882640527303186396797869)
                  ·
                    refine ⟨4080990197738694898799201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10882640527303186396797869 4080990197738694898799201)
                    ·
                      refine ⟨3060742648304021174099401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080990197738694898799201 3060742648304021174099401)
                      ·
                        rfl

theorem cell23_5960775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_5960775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960775 prefixEnd_5960775 := by exact prefixLift 5960775
  have htrace : WordTrace (prefixWord ++ tailWord_5960775) baseStart_5960775 baseEnd_5960775 := by
    simpa [prefixWord, tailWord_5960775, baseEnd_5960775] using wordTrace_append hprefix tailTrace_5960775
  have hstable : (prefixWord ++ tailWord_5960775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960775).length < 2 ^ (prefixWord ++ tailWord_5960775).sum := by decide
  have hdescent : baseEnd_5960775 < baseStart_5960775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960788 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_5960788 : Nat := 118140960795 + 5960788 * 2 ^ 59
def prefixEnd_5960788 : Nat := 4983230072969 + 3 ^ 40 * 5960788 * 2
def baseEnd_5960788 : Nat := 3060749323552529623236841

theorem tailTrace_5960788 : CollatzResearch.WordTrace tailWord_5960788 prefixEnd_5960788 3060749323552529623236841 := by
  unfold tailWord_5960788
  simp only [CollatzResearch.WordTrace]
  refine ⟨108703899564545286193337509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144938532752727048257783345 108703899564545286193337509)
  ·
    refine ⟨20381981168352241161250783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108703899564545286193337509 20381981168352241161250783)
    ·
      refine ⟨30572971752528361741876175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20381981168352241161250783 30572971752528361741876175)
      ·
        refine ⟨45859457628792542612814263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30572971752528361741876175 45859457628792542612814263)
        ·
          refine ⟨68789186443188813919221395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45859457628792542612814263 68789186443188813919221395)
          ·
            refine ⟨103183779664783220878832093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68789186443188813919221395 103183779664783220878832093)
            ·
              refine ⟨38693917374293707829562035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103183779664783220878832093 38693917374293707829562035)
              ·
                refine ⟨58040876061440561744343053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38693917374293707829562035 58040876061440561744343053)
                ·
                  refine ⟨21765328523040210654128645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58040876061440561744343053 21765328523040210654128645)
                  ·
                    refine ⟨4080999098070039497649121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21765328523040210654128645 4080999098070039497649121)
                    ·
                      refine ⟨3060749323552529623236841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4080999098070039497649121 3060749323552529623236841)
                      ·
                        rfl

theorem cell23_5960788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_5960788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960788 prefixEnd_5960788 := by exact prefixLift 5960788
  have htrace : WordTrace (prefixWord ++ tailWord_5960788) baseStart_5960788 baseEnd_5960788 := by
    simpa [prefixWord, tailWord_5960788, baseEnd_5960788] using wordTrace_append hprefix tailTrace_5960788
  have hstable : (prefixWord ++ tailWord_5960788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960788).length < 2 ^ (prefixWord ++ tailWord_5960788).sum := by decide
  have hdescent : baseEnd_5960788 < baseStart_5960788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960794 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 11]
def baseStart_5960794 : Nat := 118140960795 + 5960794 * 2 ^ 59
def prefixEnd_5960794 : Nat := 4983230072969 + 3 ^ 40 * 5960794 * 2
def baseEnd_5960794 : Nat := 340083600492939622195757

theorem tailTrace_5960794 : CollatzResearch.WordTrace tailWord_5960794 prefixEnd_5960794 340083600492939622195757 := by
  unfold tailWord_5960794
  simp only [CollatzResearch.WordTrace]
  refine ⟨54352004491767208852848359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144938678644712556940928957 54352004491767208852848359)
  ·
    refine ⟨81528006737650813279272539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54352004491767208852848359 81528006737650813279272539)
    ·
      refine ⟨122292010106476219918908809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81528006737650813279272539 122292010106476219918908809)
      ·
        refine ⟨91719007579857164939181607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122292010106476219918908809 91719007579857164939181607)
        ·
          refine ⟨137578511369785747408772411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91719007579857164939181607 137578511369785747408772411)
          ·
            refine ⟨206367767054678621113158617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137578511369785747408772411 206367767054678621113158617)
            ·
              refine ⟨154775825291008965834868963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206367767054678621113158617 154775825291008965834868963)
              ·
                refine ⟨232163737936513448752303445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154775825291008965834868963 232163737936513448752303445)
                ·
                  refine ⟨340083600492939622195757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 232163737936513448752303445 340083600492939622195757)
                  ·
                    rfl

theorem cell23_5960794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_5960794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960794 prefixEnd_5960794 := by exact prefixLift 5960794
  have htrace : WordTrace (prefixWord ++ tailWord_5960794) baseStart_5960794 baseEnd_5960794 := by
    simpa [prefixWord, tailWord_5960794, baseEnd_5960794] using wordTrace_append hprefix tailTrace_5960794
  have hstable : (prefixWord ++ tailWord_5960794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960794).length < 2 ^ (prefixWord ++ tailWord_5960794).sum := by decide
  have hdescent : baseEnd_5960794 < baseStart_5960794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960822 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_5960822 : Nat := 118140960795 + 5960822 * 2 ^ 59
def prefixEnd_5960822 : Nat := 4983230072969 + 3 ^ 40 * 5960822 * 2
def baseEnd_5960822 : Nat := 3060766781894782490211685

theorem tailTrace_5960822 : CollatzResearch.WordTrace tailWord_5960822 prefixEnd_5960822 3060766781894782490211685 := by
  unfold tailWord_5960822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13588064950685462262088295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144939359473978264128941813 13588064950685462262088295)
  ·
    refine ⟨20382097426028193393132443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13588064950685462262088295 20382097426028193393132443)
    ·
      refine ⟨30573146139042290089698665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20382097426028193393132443 30573146139042290089698665)
      ·
        refine ⟨22929859604281717567273999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30573146139042290089698665 22929859604281717567273999)
        ·
          refine ⟨34394789406422576350910999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22929859604281717567273999 34394789406422576350910999)
          ·
            refine ⟨51592184109633864526366499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34394789406422576350910999 51592184109633864526366499)
            ·
              refine ⟨77388276164450796789549749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51592184109633864526366499 77388276164450796789549749)
              ·
                refine ⟨7255150890417262199020289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77388276164450796789549749 7255150890417262199020289)
                ·
                  refine ⟨5441363167812946649265217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255150890417262199020289 5441363167812946649265217)
                  ·
                    refine ⟨4081022375859709986948913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5441363167812946649265217 4081022375859709986948913)
                    ·
                      refine ⟨3060766781894782490211685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081022375859709986948913 3060766781894782490211685)
                      ·
                        rfl

theorem cell23_5960822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_5960822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960822 prefixEnd_5960822 := by exact prefixLift 5960822
  have htrace : WordTrace (prefixWord ++ tailWord_5960822) baseStart_5960822 baseEnd_5960822 := by
    simpa [prefixWord, tailWord_5960822, baseEnd_5960822] using wordTrace_append hprefix tailTrace_5960822
  have hstable : (prefixWord ++ tailWord_5960822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960822).length < 2 ^ (prefixWord ++ tailWord_5960822).sum := by decide
  have hdescent : baseEnd_5960822 < baseStart_5960822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960841 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 1, 7]
def baseStart_5960841 : Nat := 118140960795 + 5960841 * 2 ^ 59
def prefixEnd_5960841 : Nat := 4983230072969 + 3 ^ 40 * 5960841 * 2
def baseEnd_5960841 : Nat := 1020258846009072638624699

theorem tailTrace_5960841 : CollatzResearch.WordTrace tailWord_5960841 prefixEnd_5960841 1020258846009072638624699 := by
  unfold tailWord_5960841
  simp only [CollatzResearch.WordTrace]
  refine ⟨217409732197898562438354377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144939821465265708292236251 217409732197898562438354377)
  ·
    refine ⟨163057299148423921828765783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217409732197898562438354377 163057299148423921828765783)
    ·
      refine ⟨244585948722635882743148675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163057299148423921828765783 244585948722635882743148675)
      ·
        refine ⟨366878923083953824114723013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244585948722635882743148675 366878923083953824114723013)
        ·
          refine ⟨68789798078241342021510565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366878923083953824114723013 68789798078241342021510565)
          ·
            refine ⟨12898087139670251629033231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68789798078241342021510565 12898087139670251629033231)
            ·
              refine ⟨19347130709505377443549847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12898087139670251629033231 19347130709505377443549847)
              ·
                refine ⟨29020696064258066165324771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19347130709505377443549847 29020696064258066165324771)
                ·
                  refine ⟨43531044096387099247987157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29020696064258066165324771 43531044096387099247987157)
                  ·
                    refine ⟨1020258846009072638624699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43531044096387099247987157 1020258846009072638624699)
                    ·
                      rfl

theorem cell23_5960841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_5960841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960841 prefixEnd_5960841 := by exact prefixLift 5960841
  have htrace : WordTrace (prefixWord ++ tailWord_5960841) baseStart_5960841 baseEnd_5960841 := by
    simpa [prefixWord, tailWord_5960841, baseEnd_5960841] using wordTrace_append hprefix tailTrace_5960841
  have hstable : (prefixWord ++ tailWord_5960841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960841).length < 2 ^ (prefixWord ++ tailWord_5960841).sum := by decide
  have hdescent : baseEnd_5960841 < baseStart_5960841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960935 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 6]
def baseStart_5960935 : Nat := 118140960795 + 5960935 * 2 ^ 59
def prefixEnd_5960935 : Nat := 4983230072969 + 3 ^ 40 * 5960935 * 2
def baseEnd_5960935 : Nat := 340091645023193394233185

theorem tailTrace_5960935 : CollatzResearch.WordTrace tailWord_5960935 prefixEnd_5960935 340091645023193394233185 := by
  unfold tailWord_5960935
  simp only [CollatzResearch.WordTrace]
  refine ⟨217413160659558016492276259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144942107106372010994850839 217413160659558016492276259)
  ·
    refine ⟨326119740989337024738414389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217413160659558016492276259 326119740989337024738414389)
    ·
      refine ⟨30573725717750346069226349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326119740989337024738414389 30573725717750346069226349)
      ·
        refine ⟨11465147144156379775959881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30573725717750346069226349 11465147144156379775959881)
        ·
          refine ⟨8598860358117284831969911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11465147144156379775959881 8598860358117284831969911)
          ·
            refine ⟨12898290537175927247954867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8598860358117284831969911 12898290537175927247954867)
            ·
              refine ⟨19347435805763890871932301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12898290537175927247954867 19347435805763890871932301)
              ·
                refine ⟨7255288427161459076974613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19347435805763890871932301 7255288427161459076974613)
                ·
                  refine ⟨340091645023193394233185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7255288427161459076974613 340091645023193394233185)
                  ·
                    rfl

theorem cell23_5960935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 6].length) (baseStart_5960935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960935 prefixEnd_5960935 := by exact prefixLift 5960935
  have htrace : WordTrace (prefixWord ++ tailWord_5960935) baseStart_5960935 baseEnd_5960935 := by
    simpa [prefixWord, tailWord_5960935, baseEnd_5960935] using wordTrace_append hprefix tailTrace_5960935
  have hstable : (prefixWord ++ tailWord_5960935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960935).length < 2 ^ (prefixWord ++ tailWord_5960935).sum := by decide
  have hdescent : baseEnd_5960935 < baseStart_5960935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960951 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_5960951 : Nat := 118140960795 + 5960951 * 2 ^ 59
def prefixEnd_5960951 : Nat := 4983230072969 + 3 ^ 40 * 5960951 * 2
def baseEnd_5960951 : Nat := 3060833020899212485498591

theorem tailTrace_5960951 : CollatzResearch.WordTrace tailWord_5960951 prefixEnd_5960951 3060833020899212485498591 := by
  unfold tailWord_5960951
  simp only [CollatzResearch.WordTrace]
  refine ⟨217413744227500051224858707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144942496151666700816572471 217413744227500051224858707)
  ·
    refine ⟨326120616341250076837288061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217413744227500051224858707 326120616341250076837288061)
    ·
      refine ⟨122295231127968778813983023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326120616341250076837288061 122295231127968778813983023)
      ·
        refine ⟨183442846691953168220974535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122295231127968778813983023 183442846691953168220974535)
        ·
          refine ⟨275164270037929752331461803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183442846691953168220974535 275164270037929752331461803)
          ·
            refine ⟨412746405056894628497192705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275164270037929752331461803 412746405056894628497192705)
            ·
              refine ⟨309559803792670971372894529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412746405056894628497192705 309559803792670971372894529)
              ·
                refine ⟨232169852844503228529670897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309559803792670971372894529 232169852844503228529670897)
                ·
                  refine ⟨174127389633377421397253173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232169852844503228529670897 174127389633377421397253173)
                  ·
                    refine ⟨16324442778129133255992485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174127389633377421397253173 16324442778129133255992485)
                    ·
                      refine ⟨3060833020899212485498591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16324442778129133255992485 3060833020899212485498591)
                      ·
                        rfl

theorem cell23_5960951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_5960951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960951 prefixEnd_5960951 := by exact prefixLift 5960951
  have htrace : WordTrace (prefixWord ++ tailWord_5960951) baseStart_5960951 baseEnd_5960951 := by
    simpa [prefixWord, tailWord_5960951, baseEnd_5960951] using wordTrace_append hprefix tailTrace_5960951
  have hstable : (prefixWord ++ tailWord_5960951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960951).length < 2 ^ (prefixWord ++ tailWord_5960951).sum := by decide
  have hdescent : baseEnd_5960951 < baseStart_5960951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960965 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_5960965 : Nat := 118140960795 + 5960965 * 2 ^ 59
def prefixEnd_5960965 : Nat := 4983230072969 + 3 ^ 40 * 5960965 * 2
def baseEnd_5960965 : Nat := 1020280069876125143574509

theorem tailTrace_5960965 : CollatzResearch.WordTrace tailWord_5960965 prefixEnd_5960965 1020280069876125143574509 := by
  unfold tailWord_5960965
  simp only [CollatzResearch.WordTrace]
  refine ⟨217414254849449331615868349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144942836566299554410578899 217414254849449331615868349)
  ·
    refine ⟨81530345568543499355950631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217414254849449331615868349 81530345568543499355950631)
    ·
      refine ⟨122295518352815249033925947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81530345568543499355950631 122295518352815249033925947)
      ·
        refine ⟨183443277529222873550888921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122295518352815249033925947 183443277529222873550888921)
        ·
          refine ⟨137582458146917155163166691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183443277529222873550888921 137582458146917155163166691)
          ·
            refine ⟨206373687220375732744750037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137582458146917155163166691 206373687220375732744750037)
            ·
              refine ⟨4836883294227556236205079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 206373687220375732744750037 4836883294227556236205079)
              ·
                refine ⟨7255324941341334354307619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836883294227556236205079 7255324941341334354307619)
                ·
                  refine ⟨10882987412012001531461429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7255324941341334354307619 10882987412012001531461429)
                  ·
                    refine ⟨1020280069876125143574509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10882987412012001531461429 1020280069876125143574509)
                    ·
                      rfl

theorem cell23_5960965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_5960965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960965 prefixEnd_5960965 := by exact prefixLift 5960965
  have htrace : WordTrace (prefixWord ++ tailWord_5960965) baseStart_5960965 baseEnd_5960965 := by
    simpa [prefixWord, tailWord_5960965, baseEnd_5960965] using wordTrace_append hprefix tailTrace_5960965
  have hstable : (prefixWord ++ tailWord_5960965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960965).length < 2 ^ (prefixWord ++ tailWord_5960965).sum := by decide
  have hdescent : baseEnd_5960965 < baseStart_5960965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960985 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 9, 2, 2]
def baseStart_5960985 : Nat := 118140960795 + 5960985 * 2 ^ 59
def prefixEnd_5960985 : Nat := 4983230072969 + 3 ^ 40 * 5960985 * 2
def baseEnd_5960985 : Nat := 3060850479241465352473435

theorem tailTrace_5960985 : CollatzResearch.WordTrace tailWord_5960985 prefixEnd_5960985 3060850479241465352473435 := by
  unfold tailWord_5960985
  simp only [CollatzResearch.WordTrace]
  refine ⟨217414984309376875031596409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144943322872917916687730939 217414984309376875031596409)
  ·
    refine ⟨163061238232032656273697307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217414984309376875031596409 163061238232032656273697307)
    ·
      refine ⟨244591857348048984410545961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163061238232032656273697307 244591857348048984410545961)
      ·
        refine ⟨183443893011036738307909471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244591857348048984410545961 183443893011036738307909471)
        ·
          refine ⟨275165839516555107461864207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183443893011036738307909471 275165839516555107461864207)
          ·
            refine ⟨412748759274832661192796311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275165839516555107461864207 412748759274832661192796311)
            ·
              refine ⟨619123138912248991789194467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412748759274832661192796311 619123138912248991789194467)
              ·
                refine ⟨928684708368373487683791701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619123138912248991789194467 928684708368373487683791701)
                ·
                  refine ⟨5441511963095938404397217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 928684708368373487683791701 5441511963095938404397217)
                  ·
                    refine ⟨4081133972321953803297913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5441511963095938404397217 4081133972321953803297913)
                    ·
                      refine ⟨3060850479241465352473435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081133972321953803297913 3060850479241465352473435)
                      ·
                        rfl

theorem cell23_5960985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_5960985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960985 prefixEnd_5960985 := by exact prefixLift 5960985
  have htrace : WordTrace (prefixWord ++ tailWord_5960985) baseStart_5960985 baseEnd_5960985 := by
    simpa [prefixWord, tailWord_5960985, baseEnd_5960985] using wordTrace_append hprefix tailTrace_5960985
  have hstable : (prefixWord ++ tailWord_5960985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960985).length < 2 ^ (prefixWord ++ tailWord_5960985).sum := by decide
  have hdescent : baseEnd_5960985 < baseStart_5960985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960988 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5960988 : Nat := 118140960795 + 5960988 * 2 ^ 59
def prefixEnd_5960988 : Nat := 4983230072969 + 3 ^ 40 * 5960988 * 2
def baseEnd_5960988 : Nat := 3060852019683428840735921

theorem tailTrace_5960988 : CollatzResearch.WordTrace tailWord_5960988 prefixEnd_5960988 3060852019683428840735921 := by
  unfold tailWord_5960988
  simp only [CollatzResearch.WordTrace]
  refine ⟨108707546864183003271977809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144943395818910671029303745 108707546864183003271977809)
  ·
    refine ⟨81530660148137252453983357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108707546864183003271977809 81530660148137252453983357)
    ·
      refine ⟨30573997555551469670243759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81530660148137252453983357 30573997555551469670243759)
      ·
        refine ⟨45860996333327204505365639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30573997555551469670243759 45860996333327204505365639)
        ·
          refine ⟨68791494499990806758048459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45860996333327204505365639 68791494499990806758048459)
          ·
            refine ⟨103187241749986210137072689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68791494499990806758048459 103187241749986210137072689)
            ·
              refine ⟨77390431312489657602804517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103187241749986210137072689 77390431312489657602804517)
              ·
                refine ⟨14510705871091810800525847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77390431312489657602804517 14510705871091810800525847)
                ·
                  refine ⟨21766058806637716200788771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14510705871091810800525847 21766058806637716200788771)
                  ·
                    refine ⟨32649088209956574301183157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21766058806637716200788771 32649088209956574301183157)
                    ·
                      refine ⟨3060852019683428840735921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32649088209956574301183157 3060852019683428840735921)
                      ·
                        rfl

theorem cell23_5960988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5960988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960988 prefixEnd_5960988 := by exact prefixLift 5960988
  have htrace : WordTrace (prefixWord ++ tailWord_5960988) baseStart_5960988 baseEnd_5960988 := by
    simpa [prefixWord, tailWord_5960988, baseEnd_5960988] using wordTrace_append hprefix tailTrace_5960988
  have hstable : (prefixWord ++ tailWord_5960988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960988).length < 2 ^ (prefixWord ++ tailWord_5960988).sum := by decide
  have hdescent : baseEnd_5960988 < baseStart_5960988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5960995 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 2, 4]
def baseStart_5960995 : Nat := 118140960795 + 5960995 * 2 ^ 59
def prefixEnd_5960995 : Nat := 4983230072969 + 3 ^ 40 * 5960995 * 2
def baseEnd_5960995 : Nat := 1020285204682670104449463

theorem tailTrace_5960995 : CollatzResearch.WordTrace tailWord_5960995 prefixEnd_5960995 1020285204682670104449463 := by
  unfold tailWord_5960995
  simp only [CollatzResearch.WordTrace]
  refine ⟨217415349039340646739460439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144943566026227097826306959 217415349039340646739460439)
  ·
    refine ⟨326123023559010970109190659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217415349039340646739460439 326123023559010970109190659)
    ·
      refine ⟨489184535338516455163785989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326123023559010970109190659 489184535338516455163785989)
      ·
        refine ⟨91722100375971835343209873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 489184535338516455163785989 91722100375971835343209873)
        ·
          refine ⟨68791575281978876507407405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91722100375971835343209873 68791575281978876507407405)
          ·
            refine ⟨25796840730742078690277777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68791575281978876507407405 25796840730742078690277777)
            ·
              refine ⟨19347630548056559017708333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25796840730742078690277777 19347630548056559017708333)
              ·
                refine ⟨7255361455521209631640625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19347630548056559017708333 7255361455521209631640625)
                ·
                  refine ⟨5441521091640907223730469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255361455521209631640625 5441521091640907223730469)
                  ·
                    refine ⟨1020285204682670104449463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5441521091640907223730469 1020285204682670104449463)
                    ·
                      rfl

theorem cell23_5960995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 4].length) (baseStart_5960995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5960995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5960995 prefixEnd_5960995 := by exact prefixLift 5960995
  have htrace : WordTrace (prefixWord ++ tailWord_5960995) baseStart_5960995 baseEnd_5960995 := by
    simpa [prefixWord, tailWord_5960995, baseEnd_5960995] using wordTrace_append hprefix tailTrace_5960995
  have hstable : (prefixWord ++ tailWord_5960995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5960995).length < 2 ^ (prefixWord ++ tailWord_5960995).sum := by decide
  have hdescent : baseEnd_5960995 < baseStart_5960995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5960995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961008 : List Nat := [2, 1, 1, 1, 2, 2, 7, 7]
def baseStart_5961008 : Nat := 118140960795 + 5961008 * 2 ^ 59
def prefixEnd_5961008 : Nat := 4983230072969 + 3 ^ 40 * 5961008 * 2
def baseEnd_5961008 : Nat := 113365269973945139351327

theorem tailTrace_5961008 : CollatzResearch.WordTrace tailWord_5961008 prefixEnd_5961008 113365269973945139351327 := by
  unfold tailWord_5961008
  simp only [CollatzResearch.WordTrace]
  refine ⟨108707911594146774979841839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144943882125529033306455785 108707911594146774979841839)
  ·
    refine ⟨163061867391220162469762759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108707911594146774979841839 163061867391220162469762759)
    ·
      refine ⟨244592801086830243704644139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163061867391220162469762759 244592801086830243704644139)
      ·
        refine ⟨366889201630245365556966209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244592801086830243704644139 366889201630245365556966209)
        ·
          refine ⟨275166901222684024167724657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366889201630245365556966209 275166901222684024167724657)
          ·
            refine ⟨206375175917013018125793493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275166901222684024167724657 206375175917013018125793493)
            ·
              refine ⟨4836918185554992612323285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 206375175917013018125793493 4836918185554992612323285)
              ·
                refine ⟨113365269973945139351327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4836918185554992612323285 113365269973945139351327)
                ·
                  rfl

theorem cell23_5961008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 7].length) (baseStart_5961008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961008 prefixEnd_5961008 := by exact prefixLift 5961008
  have htrace : WordTrace (prefixWord ++ tailWord_5961008) baseStart_5961008 baseEnd_5961008 := by
    simpa [prefixWord, tailWord_5961008, baseEnd_5961008] using wordTrace_append hprefix tailTrace_5961008
  have hstable : (prefixWord ++ tailWord_5961008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961008).length < 2 ^ (prefixWord ++ tailWord_5961008).sum := by decide
  have hdescent : baseEnd_5961008 < baseStart_5961008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961022 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_5961022 : Nat := 118140960795 + 5961022 * 2 ^ 59
def prefixEnd_5961022 : Nat := 4983230072969 + 3 ^ 40 * 5961022 * 2
def baseEnd_5961022 : Nat := 3060869478025681707710765

theorem tailTrace_5961022 : CollatzResearch.WordTrace tailWord_5961022 prefixEnd_5961022 3060869478025681707710765 := by
  unfold tailWord_5961022
  simp only [CollatzResearch.WordTrace]
  refine ⟨27177041726280353793836665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144944222540161886900462213 27177041726280353793836665)
  ·
    refine ⟨20382781294710265345377499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27177041726280353793836665 20382781294710265345377499)
    ·
      refine ⟨30574171942065398018066249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20382781294710265345377499 30574171942065398018066249)
      ·
        refine ⟨22930628956549048513549687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30574171942065398018066249 22930628956549048513549687)
        ·
          refine ⟨34395943434823572770324531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22930628956549048513549687 34395943434823572770324531)
          ·
            refine ⟨51593915152235359155486797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34395943434823572770324531 51593915152235359155486797)
            ·
              refine ⟨19347718182088259683307549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51593915152235359155486797 19347718182088259683307549)
              ·
                refine ⟨7255394318283097381240331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19347718182088259683307549 7255394318283097381240331)
                ·
                  refine ⟨10883091477424646071860497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7255394318283097381240331 10883091477424646071860497)
                  ·
                    refine ⟨8162318608068484553895373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10883091477424646071860497 8162318608068484553895373)
                    ·
                      refine ⟨3060869478025681707710765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8162318608068484553895373 3060869478025681707710765)
                      ·
                        rfl

theorem cell23_5961022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_5961022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961022 prefixEnd_5961022 := by exact prefixLift 5961022
  have htrace : WordTrace (prefixWord ++ tailWord_5961022) baseStart_5961022 baseEnd_5961022 := by
    simpa [prefixWord, tailWord_5961022, baseEnd_5961022] using wordTrace_append hprefix tailTrace_5961022
  have hstable : (prefixWord ++ tailWord_5961022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961022).length < 2 ^ (prefixWord ++ tailWord_5961022).sum := by decide
  have hdescent : baseEnd_5961022 < baseStart_5961022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961070 : List Nat := [4, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5961070 : Nat := 118140960795 + 5961070 * 2 ^ 59
def prefixEnd_5961070 : Nat := 4983230072969 + 3 ^ 40 * 5961070 * 2
def baseEnd_5961070 : Nat := 3060894125097097519910545

theorem tailTrace_5961070 : CollatzResearch.WordTrace tailWord_5961070 prefixEnd_5961070 3060894125097097519910545 := by
  unfold tailWord_5961070
  simp only [CollatzResearch.WordTrace]
  refine ⟨27177260564258616818555083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144945389676045956365627109 27177260564258616818555083)
  ·
    refine ⟨40765890846387925227832625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27177260564258616818555083 40765890846387925227832625)
    ·
      refine ⟨30574418134790943920874469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40765890846387925227832625 30574418134790943920874469)
      ·
        refine ⟨5732703400273301985163963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30574418134790943920874469 5732703400273301985163963)
        ·
          refine ⟨8599055100409952977745945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732703400273301985163963 8599055100409952977745945)
          ·
            refine ⟨6449291325307464733309459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8599055100409952977745945 6449291325307464733309459)
            ·
              refine ⟨9673936987961197099964189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6449291325307464733309459 9673936987961197099964189)
              ·
                refine ⟨3627726370485448912486571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9673936987961197099964189 3627726370485448912486571)
                ·
                  refine ⟨5441589555728173368729857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3627726370485448912486571 5441589555728173368729857)
                  ·
                    refine ⟨4081192166796130026547393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5441589555728173368729857 4081192166796130026547393)
                    ·
                      refine ⟨3060894125097097519910545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081192166796130026547393 3060894125097097519910545)
                      ·
                        rfl

theorem cell23_5961070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5961070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961070 prefixEnd_5961070 := by exact prefixLift 5961070
  have htrace : WordTrace (prefixWord ++ tailWord_5961070) baseStart_5961070 baseEnd_5961070 := by
    simpa [prefixWord, tailWord_5961070, baseEnd_5961070] using wordTrace_append hprefix tailTrace_5961070
  have hstable : (prefixWord ++ tailWord_5961070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961070).length < 2 ^ (prefixWord ++ tailWord_5961070).sum := by decide
  have hdescent : baseEnd_5961070 < baseStart_5961070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961088 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_5961088 : Nat := 118140960795 + 5961088 * 2 ^ 59
def prefixEnd_5961088 : Nat := 4983230072969 + 3 ^ 40 * 5961088 * 2
def baseEnd_5961088 : Nat := 3060903367748878449485461

theorem tailTrace_5961088 : CollatzResearch.WordTrace tailWord_5961088 prefixEnd_5961088 3060903367748878449485461 := by
  unfold tailWord_5961088
  simp only [CollatzResearch.WordTrace]
  refine ⟨108709370514001861811297959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144945827352002482415063945 108709370514001861811297959)
  ·
    refine ⟨163064055771002792716946939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108709370514001861811297959 163064055771002792716946939)
    ·
      refine ⟨244596083656504189075420409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163064055771002792716946939 244596083656504189075420409)
      ·
        refine ⟨183447062742378141806565307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244596083656504189075420409 183447062742378141806565307)
        ·
          refine ⟨275170594113567212709847961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183447062742378141806565307 275170594113567212709847961)
          ·
            refine ⟨206377945585175409532385971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275170594113567212709847961 206377945585175409532385971)
            ·
              refine ⟨309566918377763114298578957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206377945585175409532385971 309566918377763114298578957)
              ·
                refine ⟨116087594391661167861967109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 309566918377763114298578957 116087594391661167861967109)
                ·
                  refine ⟨21766423948436468974118833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116087594391661167861967109 21766423948436468974118833)
                  ·
                    refine ⟨16324817961327351730589125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21766423948436468974118833 16324817961327351730589125)
                    ·
                      refine ⟨3060903367748878449485461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16324817961327351730589125 3060903367748878449485461)
                      ·
                        rfl

theorem cell23_5961088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_5961088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961088 prefixEnd_5961088 := by exact prefixLift 5961088
  have htrace : WordTrace (prefixWord ++ tailWord_5961088) baseStart_5961088 baseEnd_5961088 := by
    simpa [prefixWord, tailWord_5961088, baseEnd_5961088] using wordTrace_append hprefix tailTrace_5961088
  have hstable : (prefixWord ++ tailWord_5961088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961088).length < 2 ^ (prefixWord ++ tailWord_5961088).sum := by decide
  have hdescent : baseEnd_5961088 < baseStart_5961088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961135 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 4, 5, 2]
def baseStart_5961135 : Nat := 118140960795 + 5961135 * 2 ^ 59
def prefixEnd_5961135 : Nat := 4983230072969 + 3 ^ 40 * 5961135 * 2
def baseEnd_5961135 : Nat := 3060927501339639765597745

theorem tailTrace_5961135 : CollatzResearch.WordTrace tailWord_5961135 prefixEnd_5961135 3060927501339639765597745 := by
  unfold tailWord_5961135
  simp only [CollatzResearch.WordTrace]
  refine ⟨217420455258833450649556859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144946970172555633766371239 217420455258833450649556859)
  ·
    refine ⟨326130682888250175974335289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217420455258833450649556859 326130682888250175974335289)
    ·
      refine ⟨244598012166187631980751467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326130682888250175974335289 244598012166187631980751467)
      ·
        refine ⟨366897018249281447971127201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244598012166187631980751467 366897018249281447971127201)
        ·
          refine ⟨275172763686961085978345401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366897018249281447971127201 275172763686961085978345401)
          ·
            refine ⟨206379572765220814483759051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275172763686961085978345401 206379572765220814483759051)
            ·
              refine ⟨309569359147831221725638577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206379572765220814483759051 309569359147831221725638577)
              ·
                refine ⟨232177019360873416294228933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309569359147831221725638577 232177019360873416294228933)
                ·
                  refine ⟨43533191130163765555167925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232177019360873416294228933 43533191130163765555167925)
                  ·
                    refine ⟨4081236668452853020796993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43533191130163765555167925 4081236668452853020796993)
                    ·
                      refine ⟨3060927501339639765597745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081236668452853020796993 3060927501339639765597745)
                      ·
                        rfl

theorem cell23_5961135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5, 2].length) (baseStart_5961135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961135 prefixEnd_5961135 := by exact prefixLift 5961135
  have htrace : WordTrace (prefixWord ++ tailWord_5961135) baseStart_5961135 baseEnd_5961135 := by
    simpa [prefixWord, tailWord_5961135, baseEnd_5961135] using wordTrace_append hprefix tailTrace_5961135
  have hstable : (prefixWord ++ tailWord_5961135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961135).length < 2 ^ (prefixWord ++ tailWord_5961135).sum := by decide
  have hdescent : baseEnd_5961135 < baseStart_5961135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961168 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_5961168 : Nat := 118140960795 + 5961168 * 2 ^ 59
def prefixEnd_5961168 : Nat := 4983230072969 + 3 ^ 40 * 5961168 * 2
def baseEnd_5961168 : Nat := 3060944446201238136485093

theorem tailTrace_5961168 : CollatzResearch.WordTrace tailWord_5961168 prefixEnd_5961168 3060944446201238136485093 := by
  unfold tailWord_5961168
  simp only [CollatzResearch.WordTrace]
  refine ⟨108710829433856948642754079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144947772578475931523672105 108710829433856948642754079)
  ·
    refine ⟨163066244150785422964131119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108710829433856948642754079 163066244150785422964131119)
    ·
      refine ⟨244599366226178134446196679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163066244150785422964131119 244599366226178134446196679)
      ·
        refine ⟨366899049339267201669295019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244599366226178134446196679 366899049339267201669295019)
        ·
          refine ⟨550348574008900802503942529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366899049339267201669295019 550348574008900802503942529)
          ·
            refine ⟨412761430506675601877956897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550348574008900802503942529 412761430506675601877956897)
            ·
              refine ⟨309571072880006701408467673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412761430506675601877956897 309571072880006701408467673)
              ·
                refine ⟨232178304660005026056350755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309571072880006701408467673 232178304660005026056350755)
                ·
                  refine ⟨348267456990007539084526133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232178304660005026056350755 348267456990007539084526133)
                  ·
                    refine ⟨32650074092813206789174325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 348267456990007539084526133 32650074092813206789174325)
                    ·
                      refine ⟨3060944446201238136485093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32650074092813206789174325 3060944446201238136485093)
                      ·
                        rfl

theorem cell23_5961168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_5961168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961168 prefixEnd_5961168 := by exact prefixLift 5961168
  have htrace : WordTrace (prefixWord ++ tailWord_5961168) baseStart_5961168 baseEnd_5961168 := by
    simpa [prefixWord, tailWord_5961168, baseEnd_5961168] using wordTrace_append hprefix tailTrace_5961168
  have hstable : (prefixWord ++ tailWord_5961168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961168).length < 2 ^ (prefixWord ++ tailWord_5961168).sum := by decide
  have hdescent : baseEnd_5961168 < baseStart_5961168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961285 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_5961285 : Nat := 118140960795 + 5961285 * 2 ^ 59
def prefixEnd_5961285 : Nat := 4983230072969 + 3 ^ 40 * 5961285 * 2
def baseEnd_5961285 : Nat := 3061004523437814178722055

theorem tailTrace_5961285 : CollatzResearch.WordTrace tailWord_5961285 prefixEnd_5961285 3061004523437814178722055 := by
  unfold tailWord_5961285
  simp only [CollatzResearch.WordTrace]
  refine ⟨217425926208290026267517309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144950617472193350845011539 217425926208290026267517309)
  ·
    refine ⟨81534722328108759850318991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217425926208290026267517309 81534722328108759850318991)
    ·
      refine ⟨122302083492163139775478487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81534722328108759850318991 122302083492163139775478487)
      ·
        refine ⟨183453125238244709663217731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122302083492163139775478487 183453125238244709663217731)
        ·
          refine ⟨275179687857367064494826597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183453125238244709663217731 275179687857367064494826597)
          ·
            refine ⟨51596191473256324592779987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275179687857367064494826597 51596191473256324592779987)
            ·
              refine ⟨77394287209884486889169981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51596191473256324592779987 77394287209884486889169981)
              ·
                refine ⟨29022857703706682583438743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77394287209884486889169981 29022857703706682583438743)
                ·
                  refine ⟨43534286555560023875158115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29022857703706682583438743 43534286555560023875158115)
                  ·
                    refine ⟨65301429833340035812737173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43534286555560023875158115 65301429833340035812737173)
                    ·
                      refine ⟨3061004523437814178722055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65301429833340035812737173 3061004523437814178722055)
                      ·
                        rfl

theorem cell23_5961285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_5961285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961285 prefixEnd_5961285 := by exact prefixLift 5961285
  have htrace : WordTrace (prefixWord ++ tailWord_5961285) baseStart_5961285 baseEnd_5961285 := by
    simpa [prefixWord, tailWord_5961285, baseEnd_5961285] using wordTrace_append hprefix tailTrace_5961285
  have hstable : (prefixWord ++ tailWord_5961285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961285).length < 2 ^ (prefixWord ++ tailWord_5961285).sum := by decide
  have hdescent : baseEnd_5961285 < baseStart_5961285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961286 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5961286 : Nat := 118140960795 + 5961286 * 2 ^ 59
def prefixEnd_5961286 : Nat := 4983230072969 + 3 ^ 40 * 5961286 * 2
def baseEnd_5961286 : Nat := 1020335012306156224936517

theorem tailTrace_5961286 : CollatzResearch.WordTrace tailWord_5961286 prefixEnd_5961286 1020335012306156224936517 := by
  unfold tailWord_5961286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794561333790200107446991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144950641787524268958869141 6794561333790200107446991)
  ·
    refine ⟨10191842000685300161170487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6794561333790200107446991 10191842000685300161170487)
    ·
      refine ⟨15287763001027950241755731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10191842000685300161170487 15287763001027950241755731)
      ·
        refine ⟨22931644501541925362633597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15287763001027950241755731 22931644501541925362633597)
        ·
          refine ⟨8599366688078222010987599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22931644501541925362633597 8599366688078222010987599)
          ·
            refine ⟨12899050032117333016481399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8599366688078222010987599 12899050032117333016481399)
            ·
              refine ⟨19348575048175999524722099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12899050032117333016481399 19348575048175999524722099)
              ·
                refine ⟨29022862572263999287083149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19348575048175999524722099 29022862572263999287083149)
                ·
                  refine ⟨10883573464598999732656181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29022862572263999287083149 10883573464598999732656181)
                  ·
                    refine ⟨1020335012306156224936517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10883573464598999732656181 1020335012306156224936517)
                    ·
                      rfl

theorem cell23_5961286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5961286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961286 prefixEnd_5961286 := by exact prefixLift 5961286
  have htrace : WordTrace (prefixWord ++ tailWord_5961286) baseStart_5961286 baseEnd_5961286 := by
    simpa [prefixWord, tailWord_5961286, baseEnd_5961286] using wordTrace_append hprefix tailTrace_5961286
  have hstable : (prefixWord ++ tailWord_5961286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961286).length < 2 ^ (prefixWord ++ tailWord_5961286).sum := by decide
  have hdescent : baseEnd_5961286 < baseStart_5961286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961289 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 3, 2, 2]
def baseStart_5961289 : Nat := 118140960795 + 5961289 * 2 ^ 59
def prefixEnd_5961289 : Nat := 4983230072969 + 3 ^ 40 * 5961289 * 2
def baseEnd_5961289 : Nat := 3061006577360432163072037

theorem tailTrace_5961289 : CollatzResearch.WordTrace tailWord_5961289 prefixEnd_5961289 3061006577360432163072037 := by
  unfold tailWord_5961289
  simp only [CollatzResearch.WordTrace]
  refine ⟨217426072100275534950662921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144950714733517023300441947 217426072100275534950662921)
  ·
    refine ⟨163069554075206651212997191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217426072100275534950662921 163069554075206651212997191)
    ·
      refine ⟨244604331112809976819495787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163069554075206651212997191 244604331112809976819495787)
      ·
        refine ⟨366906496669214965229243681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244604331112809976819495787 366906496669214965229243681)
        ·
          refine ⟨275179872501911223921932761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366906496669214965229243681 275179872501911223921932761)
          ·
            refine ⟨206384904376433417941449571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275179872501911223921932761 206384904376433417941449571)
            ·
              refine ⟨309577356564650126912174357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206384904376433417941449571 309577356564650126912174357)
              ·
                refine ⟨14511438588967974699008173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 309577356564650126912174357 14511438588967974699008173)
                ·
                  refine ⟨5441789470862990512128065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14511438588967974699008173 5441789470862990512128065)
                  ·
                    refine ⟨4081342103147242884096049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5441789470862990512128065 4081342103147242884096049)
                    ·
                      refine ⟨3061006577360432163072037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081342103147242884096049 3061006577360432163072037)
                      ·
                        rfl

theorem cell23_5961289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 2, 2].length) (baseStart_5961289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961289 prefixEnd_5961289 := by exact prefixLift 5961289
  have htrace : WordTrace (prefixWord ++ tailWord_5961289) baseStart_5961289 baseEnd_5961289 := by
    simpa [prefixWord, tailWord_5961289, baseEnd_5961289] using wordTrace_append hprefix tailTrace_5961289
  have hstable : (prefixWord ++ tailWord_5961289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961289).length < 2 ^ (prefixWord ++ tailWord_5961289).sum := by decide
  have hdescent : baseEnd_5961289 < baseStart_5961289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961293 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_5961293 : Nat := 118140960795 + 5961293 * 2 ^ 59
def prefixEnd_5961293 : Nat := 4983230072969 + 3 ^ 40 * 5961293 * 2
def baseEnd_5961293 : Nat := 3061008631283050147422019

theorem tailTrace_5961293 : CollatzResearch.WordTrace tailWord_5961293 prefixEnd_5961293 3061008631283050147422019 := by
  unfold tailWord_5961293
  simp only [CollatzResearch.WordTrace]
  refine ⟨217426217992261043633808533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144950811994840695755872355 217426217992261043633808533)
  ·
    refine ⟨10191853968387236420334775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217426217992261043633808533 10191853968387236420334775)
    ·
      refine ⟨15287780952580854630502163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10191853968387236420334775 15287780952580854630502163)
      ·
        refine ⟨22931671428871281945753245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15287780952580854630502163 22931671428871281945753245)
        ·
          refine ⟨8599376785826730729657467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22931671428871281945753245 8599376785826730729657467)
          ·
            refine ⟨12899065178740096094486201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8599376785826730729657467 12899065178740096094486201)
            ·
              refine ⟨9674298884055072070864651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12899065178740096094486201 9674298884055072070864651)
              ·
                refine ⟨14511448326082608106296977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9674298884055072070864651 14511448326082608106296977)
                ·
                  refine ⟨10883586244561956079722733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14511448326082608106296977 10883586244561956079722733)
                  ·
                    refine ⟨4081344841710733529896025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10883586244561956079722733 4081344841710733529896025)
                    ·
                      refine ⟨3061008631283050147422019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081344841710733529896025 3061008631283050147422019)
                      ·
                        rfl

theorem cell23_5961293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_5961293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961293 prefixEnd_5961293 := by exact prefixLift 5961293
  have htrace : WordTrace (prefixWord ++ tailWord_5961293) baseStart_5961293 baseEnd_5961293 := by
    simpa [prefixWord, tailWord_5961293, baseEnd_5961293] using wordTrace_append hprefix tailTrace_5961293
  have hstable : (prefixWord ++ tailWord_5961293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961293).length < 2 ^ (prefixWord ++ tailWord_5961293).sum := by decide
  have hdescent : baseEnd_5961293 < baseStart_5961293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961335 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_5961335 : Nat := 118140960795 + 5961335 * 2 ^ 59
def prefixEnd_5961335 : Nat := 4983230072969 + 3 ^ 40 * 5961335 * 2
def baseEnd_5961335 : Nat := 3061030197470538983096825

theorem tailTrace_5961335 : CollatzResearch.WordTrace tailWord_5961335 prefixEnd_5961335 3061030197470538983096825 := by
  unfold tailWord_5961335
  simp only [CollatzResearch.WordTrace]
  refine ⟨217427749858108884806837459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144951833238739256537891639 217427749858108884806837459)
  ·
    refine ⟨326141624787163327210256189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217427749858108884806837459 326141624787163327210256189)
    ·
      refine ⟨122303109295186247703846071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326141624787163327210256189 122303109295186247703846071)
      ·
        refine ⟨183454663942779371555769107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122303109295186247703846071 183454663942779371555769107)
        ·
          refine ⟨275181995914169057333653661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183454663942779371555769107 275181995914169057333653661)
          ·
            refine ⟨103193248467813396500120123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275181995914169057333653661 103193248467813396500120123)
            ·
              refine ⟨154789872701720094750180185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103193248467813396500120123 154789872701720094750180185)
              ·
                refine ⟨116092404526290071062635139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154789872701720094750180185 116092404526290071062635139)
                ·
                  refine ⟨174138606789435106593952709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116092404526290071062635139 174138606789435106593952709)
                  ·
                    refine ⟨32650988773019082486366133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174138606789435106593952709 32650988773019082486366133)
                    ·
                      refine ⟨3061030197470538983096825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32650988773019082486366133 3061030197470538983096825)
                      ·
                        rfl

theorem cell23_5961335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_5961335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961335 prefixEnd_5961335 := by exact prefixLift 5961335
  have htrace : WordTrace (prefixWord ++ tailWord_5961335) baseStart_5961335 baseEnd_5961335 := by
    simpa [prefixWord, tailWord_5961335, baseEnd_5961335] using wordTrace_append hprefix tailTrace_5961335
  have hstable : (prefixWord ++ tailWord_5961335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961335).length < 2 ^ (prefixWord ++ tailWord_5961335).sum := by decide
  have hdescent : baseEnd_5961335 < baseStart_5961335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961339 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 3]
def baseStart_5961339 : Nat := 118140960795 + 5961339 * 2 ^ 59
def prefixEnd_5961339 : Nat := 4983230072969 + 3 ^ 40 * 5961339 * 2
def baseEnd_5961339 : Nat := 3061032251393156967446807

theorem tailTrace_5961339 : CollatzResearch.WordTrace tailWord_5961339 prefixEnd_5961339 3061032251393156967446807 := by
  unfold tailWord_5961339
  simp only [CollatzResearch.WordTrace]
  refine ⟨217427895750094393489983071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144951930500062928993322047 217427895750094393489983071)
  ·
    refine ⟨326141843625141590234974607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217427895750094393489983071 326141843625141590234974607)
    ·
      refine ⟨489212765437712385352461911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326141843625141590234974607 489212765437712385352461911)
      ·
        refine ⟨733819148156568578028692867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489212765437712385352461911 733819148156568578028692867)
        ·
          refine ⟨1100728722234852867043039301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733819148156568578028692867 1100728722234852867043039301)
          ·
            refine ⟨206386635419034912570569869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1100728722234852867043039301 206386635419034912570569869)
            ·
              refine ⟨77394988282138092213963701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206386635419034912570569869 77394988282138092213963701)
              ·
                refine ⟨7255780151450446145059097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77394988282138092213963701 7255780151450446145059097)
                ·
                  refine ⟨5441835113587834608794323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7255780151450446145059097 5441835113587834608794323)
                  ·
                    refine ⟨8162752670381751913191485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5441835113587834608794323 8162752670381751913191485)
                    ·
                      refine ⟨3061032251393156967446807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8162752670381751913191485 3061032251393156967446807)
                      ·
                        rfl

theorem cell23_5961339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 3].length) (baseStart_5961339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961339 prefixEnd_5961339 := by exact prefixLift 5961339
  have htrace : WordTrace (prefixWord ++ tailWord_5961339) baseStart_5961339 baseEnd_5961339 := by
    simpa [prefixWord, tailWord_5961339, baseEnd_5961339] using wordTrace_append hprefix tailTrace_5961339
  have hstable : (prefixWord ++ tailWord_5961339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961339).length < 2 ^ (prefixWord ++ tailWord_5961339).sum := by decide
  have hdescent : baseEnd_5961339 < baseStart_5961339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961349 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 3, 3, 2]
def baseStart_5961349 : Nat := 118140960795 + 5961349 * 2 ^ 59
def prefixEnd_5961349 : Nat := 4983230072969 + 3 ^ 40 * 5961349 * 2
def baseEnd_5961349 : Nat := 3061037386199701928321761

theorem tailTrace_5961349 : CollatzResearch.WordTrace tailWord_5961349 prefixEnd_5961349 3061037386199701928321761 := by
  unfold tailWord_5961349
  simp only [CollatzResearch.WordTrace]
  refine ⟨217428260480058165197847101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144952173653372110131898067 217428260480058165197847101)
  ·
    refine ⟨81535597680021811949192663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217428260480058165197847101 81535597680021811949192663)
    ·
      refine ⟨122303396520032717923788995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81535597680021811949192663 122303396520032717923788995)
      ·
        refine ⟨183455094780049076885683493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122303396520032717923788995 183455094780049076885683493)
        ·
          refine ⟨34397830271259201916065655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183455094780049076885683493 34397830271259201916065655)
          ·
            refine ⟨51596745406888802874098483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34397830271259201916065655 51596745406888802874098483)
            ·
              refine ⟨77395118110333204311147725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51596745406888802874098483 77395118110333204311147725)
              ·
                refine ⟨29023169291374951616680397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77395118110333204311147725 29023169291374951616680397)
                ·
                  refine ⟨10883688484265606856255149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29023169291374951616680397 10883688484265606856255149)
                  ·
                    refine ⟨4081383181599602571095681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10883688484265606856255149 4081383181599602571095681)
                    ·
                      refine ⟨3061037386199701928321761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081383181599602571095681 3061037386199701928321761)
                      ·
                        rfl

theorem cell23_5961349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_5961349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961349 prefixEnd_5961349 := by exact prefixLift 5961349
  have htrace : WordTrace (prefixWord ++ tailWord_5961349) baseStart_5961349 baseEnd_5961349 := by
    simpa [prefixWord, tailWord_5961349, baseEnd_5961349] using wordTrace_append hprefix tailTrace_5961349
  have hstable : (prefixWord ++ tailWord_5961349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961349).length < 2 ^ (prefixWord ++ tailWord_5961349).sum := by decide
  have hdescent : baseEnd_5961349 < baseStart_5961349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961355 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 1, 8]
def baseStart_5961355 : Nat := 118140960795 + 5961355 * 2 ^ 59
def prefixEnd_5961355 : Nat := 4983230072969 + 3 ^ 40 * 5961355 * 2
def baseEnd_5961355 : Nat := 1020346822361209634948911

theorem tailTrace_5961355 : CollatzResearch.WordTrace tailWord_5961355 prefixEnd_5961355 1020346822361209634948911 := by
  unfold tailWord_5961355
  simp only [CollatzResearch.WordTrace]
  refine ⟨217428479318036428222565519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144952319545357618815043679 217428479318036428222565519)
  ·
    refine ⟨326142718977054642333848279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217428479318036428222565519 326142718977054642333848279)
    ·
      refine ⟨489214078465581963500772419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326142718977054642333848279 489214078465581963500772419)
      ·
        refine ⟨733821117698372945251158629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489214078465581963500772419 733821117698372945251158629)
        ·
          refine ⟨137591459568444927234592243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 733821117698372945251158629 137591459568444927234592243)
          ·
            refine ⟨206387189352667390851888365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137591459568444927234592243 206387189352667390851888365)
            ·
              refine ⟨77395196007250271569458137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206387189352667390851888365 77395196007250271569458137)
              ·
                refine ⟨58046397005437703677093603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77395196007250271569458137 58046397005437703677093603)
                ·
                  refine ⟨87069595508156555515640405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58046397005437703677093603 87069595508156555515640405)
                  ·
                    refine ⟨1020346822361209634948911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87069595508156555515640405 1020346822361209634948911)
                    ·
                      rfl

theorem cell23_5961355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_5961355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961355 prefixEnd_5961355 := by exact prefixLift 5961355
  have htrace : WordTrace (prefixWord ++ tailWord_5961355) baseStart_5961355 baseEnd_5961355 := by
    simpa [prefixWord, tailWord_5961355, baseEnd_5961355] using wordTrace_append hprefix tailTrace_5961355
  have hstable : (prefixWord ++ tailWord_5961355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961355).length < 2 ^ (prefixWord ++ tailWord_5961355).sum := by decide
  have hdescent : baseEnd_5961355 < baseStart_5961355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961390 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5961390 : Nat := 118140960795 + 5961390 * 2 ^ 59
def prefixEnd_5961390 : Nat := 4983230072969 + 3 ^ 40 * 5961390 * 2
def baseEnd_5961390 : Nat := 3061058438906536267909073

theorem tailTrace_5961390 : CollatzResearch.WordTrace tailWord_5961390 prefixEnd_5961390 3061058438906536267909073 := by
  unfold tailWord_5961390
  simp only [CollatzResearch.WordTrace]
  refine ⟨27178719484113703650011203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144953170581939752800059749 27178719484113703650011203)
  ·
    refine ⟨40768079226170555475016805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27178719484113703650011203 40768079226170555475016805)
    ·
      refine ⟨7644014854906979151565651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40768079226170555475016805 7644014854906979151565651)
      ·
        refine ⟨11466022282360468727348477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7644014854906979151565651 11466022282360468727348477)
        ·
          refine ⟨4299758355885175772755679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11466022282360468727348477 4299758355885175772755679)
          ·
            refine ⟨6449637533827763659133519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299758355885175772755679 6449637533827763659133519)
            ·
              refine ⟨9674456300741645488700279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6449637533827763659133519 9674456300741645488700279)
              ·
                refine ⟨14511684451112468233050419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9674456300741645488700279 14511684451112468233050419)
                ·
                  refine ⟨21767526676668702349575629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14511684451112468233050419 21767526676668702349575629)
                  ·
                    refine ⟨8162822503750763381090861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21767526676668702349575629 8162822503750763381090861)
                    ·
                      refine ⟨3061058438906536267909073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8162822503750763381090861 3061058438906536267909073)
                      ·
                        rfl

theorem cell23_5961390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5961390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961390 prefixEnd_5961390 := by exact prefixLift 5961390
  have htrace : WordTrace (prefixWord ++ tailWord_5961390) baseStart_5961390 baseEnd_5961390 := by
    simpa [prefixWord, tailWord_5961390, baseEnd_5961390] using wordTrace_append hprefix tailTrace_5961390
  have hstable : (prefixWord ++ tailWord_5961390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961390).length < 2 ^ (prefixWord ++ tailWord_5961390).sum := by decide
  have hdescent : baseEnd_5961390 < baseStart_5961390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961392 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_5961392 : Nat := 118140960795 + 5961392 * 2 ^ 59
def prefixEnd_5961392 : Nat := 4983230072969 + 3 ^ 40 * 5961392 * 2
def baseEnd_5961392 : Nat := 3061059465867845260084063

theorem tailTrace_5961392 : CollatzResearch.WordTrace tailWord_5961392 prefixEnd_5961392 3061059465867845260084063 := by
  unfold tailWord_5961392
  simp only [CollatzResearch.WordTrace]
  refine ⟨108714914409451191770831215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144953219212601589027774953 108714914409451191770831215)
  ·
    refine ⟨163072371614176787656246823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108714914409451191770831215 163072371614176787656246823)
    ·
      refine ⟨244608557421265181484370235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163072371614176787656246823 244608557421265181484370235)
      ·
        refine ⟨366912836131897772226555353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244608557421265181484370235 366912836131897772226555353)
        ·
          refine ⟨275184627098923329169916515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366912836131897772226555353 275184627098923329169916515)
          ·
            refine ⟨412776940648384993754874773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275184627098923329169916515 412776940648384993754874773)
            ·
              refine ⟨19348919092893046582259755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 412776940648384993754874773 19348919092893046582259755)
              ·
                refine ⟨29023378639339569873389633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19348919092893046582259755 29023378639339569873389633)
                ·
                  refine ⟨21767533979504677405042225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29023378639339569873389633 21767533979504677405042225)
                  ·
                    refine ⟨16325650484628508053781669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21767533979504677405042225 16325650484628508053781669)
                    ·
                      refine ⟨3061059465867845260084063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16325650484628508053781669 3061059465867845260084063)
                      ·
                        rfl

theorem cell23_5961392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_5961392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961392 prefixEnd_5961392 := by exact prefixLift 5961392
  have htrace : WordTrace (prefixWord ++ tailWord_5961392) baseStart_5961392 baseEnd_5961392 := by
    simpa [prefixWord, tailWord_5961392, baseEnd_5961392] using wordTrace_append hprefix tailTrace_5961392
  have hstable : (prefixWord ++ tailWord_5961392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961392).length < 2 ^ (prefixWord ++ tailWord_5961392).sum := by decide
  have hdescent : baseEnd_5961392 < baseStart_5961392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961402 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 7]
def baseStart_5961402 : Nat := 118140960795 + 5961402 * 2 ^ 59
def prefixEnd_5961402 : Nat := 4983230072969 + 3 ^ 40 * 5961402 * 2
def baseEnd_5961402 : Nat := 340118288963821135662113

theorem tailTrace_5961402 : CollatzResearch.WordTrace tailWord_5961402 prefixEnd_5961402 340118288963821135662113 := by
  unfold tailWord_5961402
  simp only [CollatzResearch.WordTrace]
  refine ⟨54357548387216538812381615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144953462365910770166350973 54357548387216538812381615)
  ·
    refine ⟨81536322580824808218572423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54357548387216538812381615 81536322580824808218572423)
    ·
      refine ⟨122304483871237212327858635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81536322580824808218572423 122304483871237212327858635)
      ·
        refine ⟨183456725806855818491787953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122304483871237212327858635 183456725806855818491787953)
        ·
          refine ⟨137592544355141863868840965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183456725806855818491787953 137592544355141863868840965)
          ·
            refine ⟨25798602066589099475407681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137592544355141863868840965 25798602066589099475407681)
            ·
              refine ⟨19348951549941824606555761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25798602066589099475407681 19348951549941824606555761)
              ·
                refine ⟨14511713662456368454916821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19348951549941824606555761 14511713662456368454916821)
                ·
                  refine ⟨340118288963821135662113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14511713662456368454916821 340118288963821135662113)
                  ·
                    rfl

theorem cell23_5961402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_5961402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961402 prefixEnd_5961402 := by exact prefixLift 5961402
  have htrace : WordTrace (prefixWord ++ tailWord_5961402) baseStart_5961402 baseEnd_5961402 := by
    simpa [prefixWord, tailWord_5961402, baseEnd_5961402] using wordTrace_append hprefix tailTrace_5961402
  have hstable : (prefixWord ++ tailWord_5961402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961402).length < 2 ^ (prefixWord ++ tailWord_5961402).sum := by decide
  have hdescent : baseEnd_5961402 < baseStart_5961402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961439 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 2, 5, 2]
def baseStart_5961439 : Nat := 118140960795 + 5961439 * 2 ^ 59
def prefixEnd_5961439 : Nat := 4983230072969 + 3 ^ 40 * 5961439 * 2
def baseEnd_5961439 : Nat := 3061083599458606576196347

theorem tailTrace_5961439 : CollatzResearch.WordTrace tailWord_5961439 prefixEnd_5961439 3061083599458606576196347 := by
  unfold tailWord_5961439
  simp only [CollatzResearch.WordTrace]
  refine ⟨217431543049732110568623371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144954362033154740379082247 217431543049732110568623371)
  ·
    refine ⟨326147314574598165852935057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217431543049732110568623371 326147314574598165852935057)
    ·
      refine ⟨244610485930948624389701293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326147314574598165852935057 244610485930948624389701293)
      ·
        refine ⟨91728932224105734146137985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244610485930948624389701293 91728932224105734146137985)
        ·
          refine ⟨68796699168079300609603489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91728932224105734146137985 68796699168079300609603489)
          ·
            refine ⟨51597524376059475457202617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68796699168079300609603489 51597524376059475457202617)
            ·
              refine ⟨38698143282044606592901963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51597524376059475457202617 38698143282044606592901963)
              ·
                refine ⟨58047214923066909889352945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38698143282044606592901963 58047214923066909889352945)
                ·
                  refine ⟨43535411192300182417014709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58047214923066909889352945 43535411192300182417014709)
                  ·
                    refine ⟨4081444799278142101595129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43535411192300182417014709 4081444799278142101595129)
                    ·
                      refine ⟨3061083599458606576196347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081444799278142101595129 3061083599458606576196347)
                      ·
                        rfl

theorem cell23_5961439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_5961439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961439 prefixEnd_5961439 := by exact prefixLift 5961439
  have htrace : WordTrace (prefixWord ++ tailWord_5961439) baseStart_5961439 baseEnd_5961439 := by
    simpa [prefixWord, tailWord_5961439, baseEnd_5961439] using wordTrace_append hprefix tailTrace_5961439
  have hstable : (prefixWord ++ tailWord_5961439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961439).length < 2 ^ (prefixWord ++ tailWord_5961439).sum := by decide
  have hdescent : baseEnd_5961439 < baseStart_5961439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961452 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_5961452 : Nat := 118140960795 + 5961452 * 2 ^ 59
def prefixEnd_5961452 : Nat := 4983230072969 + 3 ^ 40 * 5961452 * 2
def baseEnd_5961452 : Nat := 3061090274707115025333787

theorem tailTrace_5961452 : CollatzResearch.WordTrace tailWord_5961452 prefixEnd_5961452 3061090274707115025333787 := by
  unfold tailWord_5961452
  simp only [CollatzResearch.WordTrace]
  refine ⟨108716008599342506894423305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144954678132456675859231073 108716008599342506894423305)
  ·
    refine ⟨81537006449506880170817479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108716008599342506894423305 81537006449506880170817479)
    ·
      refine ⟨122305509674260320256226219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81537006449506880170817479 122305509674260320256226219)
      ·
        refine ⟨183458264511390480384339329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122305509674260320256226219 183458264511390480384339329)
        ·
          refine ⟨137593698383542860288254497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183458264511390480384339329 137593698383542860288254497)
          ·
            refine ⟨103195273787657145216190873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137593698383542860288254497 103195273787657145216190873)
            ·
              refine ⟨77396455340742858912143155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103195273787657145216190873 77396455340742858912143155)
              ·
                refine ⟨116094683011114288368214733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77396455340742858912143155 116094683011114288368214733)
                ·
                  refine ⟨43535506129167858138080525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116094683011114288368214733 43535506129167858138080525)
                  ·
                    refine ⟨16325814798437946801780197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43535506129167858138080525 16325814798437946801780197)
                    ·
                      refine ⟨3061090274707115025333787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16325814798437946801780197 3061090274707115025333787)
                      ·
                        rfl

theorem cell23_5961452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_5961452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961452 prefixEnd_5961452 := by exact prefixLift 5961452
  have htrace : WordTrace (prefixWord ++ tailWord_5961452) baseStart_5961452 baseEnd_5961452 := by
    simpa [prefixWord, tailWord_5961452, baseEnd_5961452] using wordTrace_append hprefix tailTrace_5961452
  have hstable : (prefixWord ++ tailWord_5961452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961452).length < 2 ^ (prefixWord ++ tailWord_5961452).sum := by decide
  have hdescent : baseEnd_5961452 < baseStart_5961452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961469 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_5961469 : Nat := 118140960795 + 5961469 * 2 ^ 59
def prefixEnd_5961469 : Nat := 4983230072969 + 3 ^ 40 * 5961469 * 2
def baseEnd_5961469 : Nat := 3061099003878241458821209

theorem tailTrace_5961469 : CollatzResearch.WordTrace tailWord_5961469 prefixEnd_5961469 3061099003878241458821209 := by
  unfold tailWord_5961469
  simp only [CollatzResearch.WordTrace]
  refine ⟨217432637239623425692215461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144955091493082283794810307 217432637239623425692215461)
  ·
    refine ⟨40768619482429392317290399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217432637239623425692215461 40768619482429392317290399)
    ·
      refine ⟨61152929223644088475935599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40768619482429392317290399 61152929223644088475935599)
      ·
        refine ⟨91729393835466132713903399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61152929223644088475935599 91729393835466132713903399)
        ·
          refine ⟨137594090753199199070855099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91729393835466132713903399 137594090753199199070855099)
          ·
            refine ⟨206391136129798798606282649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137594090753199199070855099 206391136129798798606282649)
            ·
              refine ⟨154793352097349098954711987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206391136129798798606282649 154793352097349098954711987)
              ·
                refine ⟨232190028146023648432067981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154793352097349098954711987 232190028146023648432067981)
                ·
                  refine ⟨87071260554758868162025493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232190028146023648432067981 87071260554758868162025493)
                  ·
                    refine ⟨4081465338504321945094945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87071260554758868162025493 4081465338504321945094945)
                    ·
                      refine ⟨3061099003878241458821209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081465338504321945094945 3061099003878241458821209)
                      ·
                        rfl

theorem cell23_5961469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_5961469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961469 prefixEnd_5961469 := by exact prefixLift 5961469
  have htrace : WordTrace (prefixWord ++ tailWord_5961469) baseStart_5961469 baseEnd_5961469 := by
    simpa [prefixWord, tailWord_5961469, baseEnd_5961469] using wordTrace_append hprefix tailTrace_5961469
  have hstable : (prefixWord ++ tailWord_5961469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961469).length < 2 ^ (prefixWord ++ tailWord_5961469).sum := by decide
  have hdescent : baseEnd_5961469 < baseStart_5961469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961509 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 6]
def baseStart_5961509 : Nat := 118140960795 + 5961509 * 2 ^ 59
def prefixEnd_5961509 : Nat := 4983230072969 + 3 ^ 40 * 5961509 * 2
def baseEnd_5961509 : Nat := 340124393678269033591225

theorem tailTrace_5961509 : CollatzResearch.WordTrace tailWord_5961509 prefixEnd_5961509 340124393678269033591225 := by
  unfold tailWord_5961509
  simp only [CollatzResearch.WordTrace]
  refine ⟨217434096159478512523671581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144956064106319008349114387 217434096159478512523671581)
  ·
    refine ⟨81537786059804442196376843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217434096159478512523671581 81537786059804442196376843)
    ·
      refine ⟨122306679089706663294565265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81537786059804442196376843 122306679089706663294565265)
      ·
        refine ⟨91730009317279997470923949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122306679089706663294565265 91730009317279997470923949)
        ·
          refine ⟨34398753493979999051596481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91730009317279997470923949 34398753493979999051596481)
          ·
            refine ⟨25799065120484999288697361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34398753493979999051596481 25799065120484999288697361)
            ·
              refine ⟨19349298840363749466523021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25799065120484999288697361 19349298840363749466523021)
              ·
                refine ⟨7255987065136406049946133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19349298840363749466523021 7255987065136406049946133)
                ·
                  refine ⟨340124393678269033591225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7255987065136406049946133 340124393678269033591225)
                  ·
                    rfl

theorem cell23_5961509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_5961509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961509 prefixEnd_5961509 := by exact prefixLift 5961509
  have htrace : WordTrace (prefixWord ++ tailWord_5961509) baseStart_5961509 baseEnd_5961509 := by
    simpa [prefixWord, tailWord_5961509, baseEnd_5961509] using wordTrace_append hprefix tailTrace_5961509
  have hstable : (prefixWord ++ tailWord_5961509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961509).length < 2 ^ (prefixWord ++ tailWord_5961509).sum := by decide
  have hdescent : baseEnd_5961509 < baseStart_5961509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961523 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 3]
def baseStart_5961523 : Nat := 118140960795 + 5961523 * 2 ^ 59
def prefixEnd_5961523 : Nat := 4983230072969 + 3 ^ 40 * 5961523 * 2
def baseEnd_5961523 : Nat := 3061126731833584247545961

theorem tailTrace_5961523 : CollatzResearch.WordTrace tailWord_5961523 prefixEnd_5961523 3061126731833584247545961 := by
  unfold tailWord_5961523
  simp only [CollatzResearch.WordTrace]
  refine ⟨217434606781427792914681223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144956404520951861943120815 217434606781427792914681223)
  ·
    refine ⟨326151910172141689372021835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217434606781427792914681223 326151910172141689372021835)
    ·
      refine ⟨489227865258212534058032753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326151910172141689372021835 489227865258212534058032753)
      ·
        refine ⟨366920898943659400543524565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489227865258212534058032753 366920898943659400543524565)
        ·
          refine ⟨8599708568992017200238857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 366920898943659400543524565 8599708568992017200238857)
          ·
            refine ⟨6449781426744012900179143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8599708568992017200238857 6449781426744012900179143)
            ·
              refine ⟨9674672140116019350268715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6449781426744012900179143 9674672140116019350268715)
              ·
                refine ⟨14512008210174029025403073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9674672140116019350268715 14512008210174029025403073)
                ·
                  refine ⟨10884006157630521769052305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14512008210174029025403073 10884006157630521769052305)
                  ·
                    refine ⟨8163004618222891326789229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10884006157630521769052305 8163004618222891326789229)
                    ·
                      refine ⟨3061126731833584247545961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163004618222891326789229 3061126731833584247545961)
                      ·
                        rfl

theorem cell23_5961523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_5961523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961523 prefixEnd_5961523 := by exact prefixLift 5961523
  have htrace : WordTrace (prefixWord ++ tailWord_5961523) baseStart_5961523 baseEnd_5961523 := by
    simpa [prefixWord, tailWord_5961523, baseEnd_5961523] using wordTrace_append hprefix tailTrace_5961523
  have hstable : (prefixWord ++ tailWord_5961523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961523).length < 2 ^ (prefixWord ++ tailWord_5961523).sum := by decide
  have hdescent : baseEnd_5961523 < baseStart_5961523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961546 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_5961546 : Nat := 118140960795 + 5961546 * 2 ^ 59
def prefixEnd_5961546 : Nat := 4983230072969 + 3 ^ 40 * 5961546 * 2
def baseEnd_5961546 : Nat := 3061138541888637657558355

theorem tailTrace_5961546 : CollatzResearch.WordTrace tailWord_5961546 prefixEnd_5961546 3061138541888637657558355 := by
  unfold tailWord_5961546
  simp only [CollatzResearch.WordTrace]
  refine ⟨54358861415086116960692123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144956963773562978561845661 54358861415086116960692123)
  ·
    refine ⟨81538292122629175441038185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54358861415086116960692123 81538292122629175441038185)
    ·
      refine ⟨61153719091971881580778639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81538292122629175441038185 61153719091971881580778639)
      ·
        refine ⟨91730578637957822371167959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61153719091971881580778639 91730578637957822371167959)
        ·
          refine ⟨137595867956936733556751939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91730578637957822371167959 137595867956936733556751939)
          ·
            refine ⟨206393801935405100335127909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137595867956936733556751939 206393801935405100335127909)
            ·
              refine ⟨38698837862888456312836483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206393801935405100335127909 38698837862888456312836483)
              ·
                refine ⟨58048256794332684469254725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38698837862888456312836483 58048256794332684469254725)
                ·
                  refine ⟨10884048148937378337985261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58048256794332684469254725 10884048148937378337985261)
                  ·
                    refine ⟨4081518055851516876744473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10884048148937378337985261 4081518055851516876744473)
                    ·
                      refine ⟨3061138541888637657558355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081518055851516876744473 3061138541888637657558355)
                      ·
                        rfl

theorem cell23_5961546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_5961546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961546 prefixEnd_5961546 := by exact prefixLift 5961546
  have htrace : WordTrace (prefixWord ++ tailWord_5961546) baseStart_5961546 baseEnd_5961546 := by
    simpa [prefixWord, tailWord_5961546, baseEnd_5961546] using wordTrace_append hprefix tailTrace_5961546
  have hstable : (prefixWord ++ tailWord_5961546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961546).length < 2 ^ (prefixWord ++ tailWord_5961546).sum := by decide
  have hdescent : baseEnd_5961546 < baseStart_5961546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961553 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_5961553 : Nat := 118140960795 + 5961553 * 2 ^ 59
def prefixEnd_5961553 : Nat := 4983230072969 + 3 ^ 40 * 5961553 * 2
def baseEnd_5961553 : Nat := 3061142136253219130170823

theorem tailTrace_5961553 : CollatzResearch.WordTrace tailWord_5961553 prefixEnd_5961553 3061142136253219130170823 := by
  unfold tailWord_5961553
  simp only [CollatzResearch.WordTrace]
  refine ⟨217435700971319108038273313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144957133980879405358848875 217435700971319108038273313)
  ·
    refine ⟨163076775728489331028704985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217435700971319108038273313 163076775728489331028704985)
    ·
      refine ⟨122307581796366998271528739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163076775728489331028704985 122307581796366998271528739)
      ·
        refine ⟨183461372694550497407293109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122307581796366998271528739 183461372694550497407293109)
        ·
          refine ⟨17199503690114109131933729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183461372694550497407293109 17199503690114109131933729)
          ·
            refine ⟨12899627767585581848950297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17199503690114109131933729 12899627767585581848950297)
            ·
              refine ⟨9674720825689186386712723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12899627767585581848950297 9674720825689186386712723)
              ·
                refine ⟨14512081238533779580069085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9674720825689186386712723 14512081238533779580069085)
                ·
                  refine ⟨5442030464450167342525907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14512081238533779580069085 5442030464450167342525907)
                  ·
                    refine ⟨8163045696675251013788861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442030464450167342525907 8163045696675251013788861)
                    ·
                      refine ⟨3061142136253219130170823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163045696675251013788861 3061142136253219130170823)
                      ·
                        rfl

theorem cell23_5961553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_5961553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961553 prefixEnd_5961553 := by exact prefixLift 5961553
  have htrace : WordTrace (prefixWord ++ tailWord_5961553) baseStart_5961553 baseEnd_5961553 := by
    simpa [prefixWord, tailWord_5961553, baseEnd_5961553] using wordTrace_append hprefix tailTrace_5961553
  have hstable : (prefixWord ++ tailWord_5961553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961553).length < 2 ^ (prefixWord ++ tailWord_5961553).sum := by decide
  have hdescent : baseEnd_5961553 < baseStart_5961553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961576 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5961576 : Nat := 118140960795 + 5961576 * 2 ^ 59
def prefixEnd_5961576 : Nat := 4983230072969 + 3 ^ 40 * 5961576 * 2
def baseEnd_5961576 : Nat := 3061153946308272540183217

theorem tailTrace_5961576 : CollatzResearch.WordTrace tailWord_5961576 prefixEnd_5961576 3061153946308272540183217 := by
  unfold tailWord_5961576
  simp only [CollatzResearch.WordTrace]
  refine ⟨108718269925117891483180291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144957693233490521977573721 108718269925117891483180291)
  ·
    refine ⟨163077404887676837224770437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108718269925117891483180291 163077404887676837224770437)
    ·
      refine ⟨30577013416439406979644457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163077404887676837224770437 30577013416439406979644457)
      ·
        refine ⟨22932760062329555234733343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30577013416439406979644457 22932760062329555234733343)
        ·
          refine ⟨34399140093494332852100015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22932760062329555234733343 34399140093494332852100015)
          ·
            refine ⟨51598710140241499278150023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34399140093494332852100015 51598710140241499278150023)
            ·
              refine ⟨77398065210362248917225035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51598710140241499278150023 77398065210362248917225035)
              ·
                refine ⟨116097097815543373375837553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77398065210362248917225035 116097097815543373375837553)
                ·
                  refine ⟨87072823361657530031878165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116097097815543373375837553 87072823361657530031878165)
                  ·
                    refine ⟨4081538595077696720244289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87072823361657530031878165 4081538595077696720244289)
                    ·
                      refine ⟨3061153946308272540183217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081538595077696720244289 3061153946308272540183217)
                      ·
                        rfl

theorem cell23_5961576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5961576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961576 prefixEnd_5961576 := by exact prefixLift 5961576
  have htrace : WordTrace (prefixWord ++ tailWord_5961576) baseStart_5961576 baseEnd_5961576 := by
    simpa [prefixWord, tailWord_5961576, baseEnd_5961576] using wordTrace_append hprefix tailTrace_5961576
  have hstable : (prefixWord ++ tailWord_5961576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961576).length < 2 ^ (prefixWord ++ tailWord_5961576).sum := by decide
  have hdescent : baseEnd_5961576 < baseStart_5961576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961620 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_5961620 : Nat := 118140960795 + 5961620 * 2 ^ 59
def prefixEnd_5961620 : Nat := 4983230072969 + 3 ^ 40 * 5961620 * 2
def baseEnd_5961620 : Nat := 1020392179819023456011005

theorem tailTrace_5961620 : CollatzResearch.WordTrace tailWord_5961620 prefixEnd_5961620 1020392179819023456011005 := by
  unfold tailWord_5961620
  simp only [CollatzResearch.WordTrace]
  refine ⟨108719072331038189240481157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144958763108050918987308209 108719072331038189240481157)
  ·
    refine ⟨20384826062069660482590217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108719072331038189240481157 20384826062069660482590217)
    ·
      refine ⟨15288619546552245361942663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20384826062069660482590217 15288619546552245361942663)
      ·
        refine ⟨22932929319828368042913995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15288619546552245361942663 22932929319828368042913995)
        ·
          refine ⟨34399393979742552064370993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22932929319828368042913995 34399393979742552064370993)
          ·
            refine ⟨25799545484806914048278245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34399393979742552064370993 25799545484806914048278245)
            ·
              refine ⟨4837414778401296384052171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25799545484806914048278245 4837414778401296384052171)
              ·
                refine ⟨7256122167601944576078257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837414778401296384052171 7256122167601944576078257)
                ·
                  refine ⟨5442091625701458432058693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7256122167601944576078257 5442091625701458432058693)
                  ·
                    refine ⟨1020392179819023456011005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5442091625701458432058693 1020392179819023456011005)
                    ·
                      rfl

theorem cell23_5961620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_5961620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961620 prefixEnd_5961620 := by exact prefixLift 5961620
  have htrace : WordTrace (prefixWord ++ tailWord_5961620) baseStart_5961620 baseEnd_5961620 := by
    simpa [prefixWord, tailWord_5961620, baseEnd_5961620] using wordTrace_append hprefix tailTrace_5961620
  have hstable : (prefixWord ++ tailWord_5961620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961620).length < 2 ^ (prefixWord ++ tailWord_5961620).sum := by decide
  have hdescent : baseEnd_5961620 < baseStart_5961620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961640 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5961640 : Nat := 118140960795 + 5961640 * 2 ^ 59
def prefixEnd_5961640 : Nat := 4983230072969 + 3 ^ 40 * 5961640 * 2
def baseEnd_5961640 : Nat := 3061186809070160289782923

theorem tailTrace_5961640 : CollatzResearch.WordTrace tailWord_5961640 prefixEnd_5961640 3061186809070160289782923 := by
  unfold tailWord_5961640
  simp only [CollatzResearch.WordTrace]
  refine ⟨108719437061001960948345187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144959249414669281264460249 108719437061001960948345187)
  ·
    refine ⟨163079155591502941422517781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108719437061001960948345187 163079155591502941422517781)
    ·
      refine ⟨7644335418351700379180521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163079155591502941422517781 7644335418351700379180521)
      ·
        refine ⟨5733251563763775284385391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7644335418351700379180521 5733251563763775284385391)
        ·
          refine ⟨8599877345645662926578087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733251563763775284385391 8599877345645662926578087)
          ·
            refine ⟨12899816018468494389867131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8599877345645662926578087 12899816018468494389867131)
            ·
              refine ⟨19349724027702741584800697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12899816018468494389867131 19349724027702741584800697)
              ·
                refine ⟨14512293020777056188600523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19349724027702741584800697 14512293020777056188600523)
                ·
                  refine ⟨21768439531165584282900785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14512293020777056188600523 21768439531165584282900785)
                  ·
                    refine ⟨16326329648374188212175589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21768439531165584282900785 16326329648374188212175589)
                    ·
                      refine ⟨3061186809070160289782923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16326329648374188212175589 3061186809070160289782923)
                      ·
                        rfl

theorem cell23_5961640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5961640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961640 prefixEnd_5961640 := by exact prefixLift 5961640
  have htrace : WordTrace (prefixWord ++ tailWord_5961640) baseStart_5961640 baseEnd_5961640 := by
    simpa [prefixWord, tailWord_5961640, baseEnd_5961640] using wordTrace_append hprefix tailTrace_5961640
  have hstable : (prefixWord ++ tailWord_5961640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961640).length < 2 ^ (prefixWord ++ tailWord_5961640).sum := by decide
  have hdescent : baseEnd_5961640 < baseStart_5961640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961669 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_5961669 : Nat := 118140960795 + 5961669 * 2 ^ 59
def prefixEnd_5961669 : Nat := 4983230072969 + 3 ^ 40 * 5961669 * 2
def baseEnd_5961669 : Nat := 3061201700009140676320289

theorem tailTrace_5961669 : CollatzResearch.WordTrace tailWord_5961669 prefixEnd_5961669 3061201700009140676320289 := by
  unfold tailWord_5961669
  simp only [CollatzResearch.WordTrace]
  refine ⟨217439931838898859849496061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144959954559265906566330707 217439931838898859849496061)
  ·
    refine ⟨81539974439587072443561023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217439931838898859849496061 81539974439587072443561023)
    ·
      refine ⟨122309961659380608665341535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81539974439587072443561023 122309961659380608665341535)
      ·
        refine ⟨183464942489070912998012303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122309961659380608665341535 183464942489070912998012303)
        ·
          refine ⟨275197413733606369497018455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183464942489070912998012303 275197413733606369497018455)
          ·
            refine ⟨412796120600409554245527683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275197413733606369497018455 412796120600409554245527683)
            ·
              refine ⟨619194180900614331368291525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412796120600409554245527683 619194180900614331368291525)
              ·
                refine ⟨116098908918865187131554661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619194180900614331368291525 116098908918865187131554661)
                ·
                  refine ⟨21768545422287222587166499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116098908918865187131554661 21768545422287222587166499)
                  ·
                    refine ⟨32652818133430833880749749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21768545422287222587166499 32652818133430833880749749)
                    ·
                      refine ⟨3061201700009140676320289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32652818133430833880749749 3061201700009140676320289)
                      ·
                        rfl

theorem cell23_5961669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_5961669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961669 prefixEnd_5961669 := by exact prefixLift 5961669
  have htrace : WordTrace (prefixWord ++ tailWord_5961669) baseStart_5961669 baseEnd_5961669 := by
    simpa [prefixWord, tailWord_5961669, baseEnd_5961669] using wordTrace_append hprefix tailTrace_5961669
  have hstable : (prefixWord ++ tailWord_5961669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961669).length < 2 ^ (prefixWord ++ tailWord_5961669).sum := by decide
  have hdescent : baseEnd_5961669 < baseStart_5961669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961676 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_5961676 : Nat := 118140960795 + 5961676 * 2 ^ 59
def prefixEnd_5961676 : Nat := 4983230072969 + 3 ^ 40 * 5961676 * 2
def baseEnd_5961676 : Nat := 1020401764791240716310919

theorem tailTrace_5961676 : CollatzResearch.WordTrace tailWord_5961676 prefixEnd_5961676 1020401764791240716310919 := by
  unfold tailWord_5961676
  simp only [CollatzResearch.WordTrace]
  refine ⟨108720093574936750022500441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144960124766582333363333921 108720093574936750022500441)
  ·
    refine ⟨81540070181202562516875331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108720093574936750022500441 81540070181202562516875331)
    ·
      refine ⟨122310105271803843775312997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81540070181202562516875331 122310105271803843775312997)
      ·
        refine ⟨22933144738463220707871187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122310105271803843775312997 22933144738463220707871187)
        ·
          refine ⟨34399717107694831061806781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22933144738463220707871187 34399717107694831061806781)
          ·
            refine ⟨12899893915385561648177543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34399717107694831061806781 12899893915385561648177543)
            ·
              refine ⟨19349840873078342472266315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12899893915385561648177543 19349840873078342472266315)
              ·
                refine ⟨29024761309617513708399473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19349840873078342472266315 29024761309617513708399473)
                ·
                  refine ⟨21768570982213135281299605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29024761309617513708399473 21768570982213135281299605)
                  ·
                    refine ⟨1020401764791240716310919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21768570982213135281299605 1020401764791240716310919)
                    ·
                      rfl

theorem cell23_5961676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_5961676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961676 prefixEnd_5961676 := by exact prefixLift 5961676
  have htrace : WordTrace (prefixWord ++ tailWord_5961676) baseStart_5961676 baseEnd_5961676 := by
    simpa [prefixWord, tailWord_5961676, baseEnd_5961676] using wordTrace_append hprefix tailTrace_5961676
  have hstable : (prefixWord ++ tailWord_5961676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961676).length < 2 ^ (prefixWord ++ tailWord_5961676).sum := by decide
  have hdescent : baseEnd_5961676 < baseStart_5961676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961780 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_5961780 : Nat := 118140960795 + 5961780 * 2 ^ 59
def prefixEnd_5961780 : Nat := 4983230072969 + 3 ^ 40 * 5961780 * 2
def baseEnd_5961780 : Nat := 3061258696361789742032279

theorem tailTrace_5961780 : CollatzResearch.WordTrace tailWord_5961780 prefixEnd_5961780 3061258696361789742032279 := by
  unfold tailWord_5961780
  simp only [CollatzResearch.WordTrace]
  refine ⟨108721990170748362903393397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144962653560997817204524529 108721990170748362903393397)
  ·
    refine ⟨10192686578507659022193131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108721990170748362903393397 10192686578507659022193131)
    ·
      refine ⟨15289029867761488533289697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10192686578507659022193131 15289029867761488533289697)
      ·
        refine ⟨11466772400821116399967273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15289029867761488533289697 11466772400821116399967273)
        ·
          refine ⟨8600079300615837299975455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11466772400821116399967273 8600079300615837299975455)
          ·
            refine ⟨12900118950923755949963183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600079300615837299975455 12900118950923755949963183)
            ·
              refine ⟨19350178426385633924944775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12900118950923755949963183 19350178426385633924944775)
              ·
                refine ⟨29025267639578450887417163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19350178426385633924944775 29025267639578450887417163)
                ·
                  refine ⟨43537901459367676331125745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29025267639578450887417163 43537901459367676331125745)
                  ·
                    refine ⟨32653426094525757248344309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43537901459367676331125745 32653426094525757248344309)
                    ·
                      refine ⟨3061258696361789742032279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32653426094525757248344309 3061258696361789742032279)
                      ·
                        rfl

theorem cell23_5961780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_5961780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961780 prefixEnd_5961780 := by exact prefixLift 5961780
  have htrace : WordTrace (prefixWord ++ tailWord_5961780) baseStart_5961780 baseEnd_5961780 := by
    simpa [prefixWord, tailWord_5961780, baseEnd_5961780] using wordTrace_append hprefix tailTrace_5961780
  have hstable : (prefixWord ++ tailWord_5961780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961780).length < 2 ^ (prefixWord ++ tailWord_5961780).sum := by decide
  have hdescent : baseEnd_5961780 < baseStart_5961780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961783 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 3, 4]
def baseStart_5961783 : Nat := 118140960795 + 5961783 * 2 ^ 59
def prefixEnd_5961783 : Nat := 4983230072969 + 3 ^ 40 * 5961783 * 2
def baseEnd_5961783 : Nat := 1020420078934584410098255

theorem tailTrace_5961783 : CollatzResearch.WordTrace tailWord_5961783 prefixEnd_5961783 1020420078934584410098255 := by
  unfold tailWord_5961783
  simp only [CollatzResearch.WordTrace]
  refine ⟨217444089760485857319146003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144962726506990571546097335 217444089760485857319146003)
  ·
    refine ⟨326166134640728785978719005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217444089760485857319146003 326166134640728785978719005)
    ·
      refine ⟨122312300490273294742019627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326166134640728785978719005 122312300490273294742019627)
      ·
        refine ⟨183468450735409942113029441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122312300490273294742019627 183468450735409942113029441)
        ·
          refine ⟨137601338051557456584772081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183468450735409942113029441 137601338051557456584772081)
          ·
            refine ⟨103201003538668092438579061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137601338051557456584772081 103201003538668092438579061)
            ·
              refine ⟨9675094081750133666116787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103201003538668092438579061 9675094081750133666116787)
              ·
                refine ⟨14512641122625200499175181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9675094081750133666116787 14512641122625200499175181)
                ·
                  refine ⟨5442240420984450187190693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14512641122625200499175181 5442240420984450187190693)
                  ·
                    refine ⟨1020420078934584410098255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5442240420984450187190693 1020420078934584410098255)
                    ·
                      rfl

theorem cell23_5961783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_5961783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961783 prefixEnd_5961783 := by exact prefixLift 5961783
  have htrace : WordTrace (prefixWord ++ tailWord_5961783) baseStart_5961783 baseEnd_5961783 := by
    simpa [prefixWord, tailWord_5961783, baseEnd_5961783] using wordTrace_append hprefix tailTrace_5961783
  have hstable : (prefixWord ++ tailWord_5961783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961783).length < 2 ^ (prefixWord ++ tailWord_5961783).sum := by decide
  have hdescent : baseEnd_5961783 < baseStart_5961783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961823 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 3]
def baseStart_5961823 : Nat := 118140960795 + 5961823 * 2 ^ 59
def prefixEnd_5961823 : Nat := 4983230072969 + 3 ^ 40 * 5961823 * 2
def baseEnd_5961823 : Nat := 3061280776029933073794581

theorem tailTrace_5961823 : CollatzResearch.WordTrace tailWord_5961823 prefixEnd_5961823 3061280776029933073794581 := by
  unfold tailWord_5961823
  simp only [CollatzResearch.WordTrace]
  refine ⟨217445548680340944150602123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144963699120227296100401415 217445548680340944150602123)
  ·
    refine ⟨326168323020511416225903185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217445548680340944150602123 326168323020511416225903185)
    ·
      refine ⟨244626242265383562169427389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326168323020511416225903185 244626242265383562169427389)
      ·
        refine ⟨91734840849518835813535271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244626242265383562169427389 91734840849518835813535271)
        ·
          refine ⟨137602261274278253720302907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91734840849518835813535271 137602261274278253720302907)
          ·
            refine ⟨206403391911417380580454361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137602261274278253720302907 206403391911417380580454361)
            ·
              refine ⟨154802543933563035435340771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206403391911417380580454361 154802543933563035435340771)
              ·
                refine ⟨232203815900344553153011157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154802543933563035435340771 232203815900344553153011157)
                ·
                  refine ⟨5442276935164325464523699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 232203815900344553153011157 5442276935164325464523699)
                  ·
                    refine ⟨8163415402746488196785549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442276935164325464523699 8163415402746488196785549)
                    ·
                      refine ⟨3061280776029933073794581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163415402746488196785549 3061280776029933073794581)
                      ·
                        rfl

theorem cell23_5961823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_5961823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961823 prefixEnd_5961823 := by exact prefixLift 5961823
  have htrace : WordTrace (prefixWord ++ tailWord_5961823) baseStart_5961823 baseEnd_5961823 := by
    simpa [prefixWord, tailWord_5961823, baseEnd_5961823] using wordTrace_append hprefix tailTrace_5961823
  have hstable : (prefixWord ++ tailWord_5961823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961823).length < 2 ^ (prefixWord ++ tailWord_5961823).sum := by decide
  have hdescent : baseEnd_5961823 < baseStart_5961823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961857 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5961857 : Nat := 118140960795 + 5961857 * 2 ^ 59
def prefixEnd_5961857 : Nat := 4983230072969 + 3 ^ 40 * 5961857 * 2
def baseEnd_5961857 : Nat := 3061298234372185940769425

theorem tailTrace_5961857 : CollatzResearch.WordTrace tailWord_5961857 prefixEnd_5961857 3061298234372185940769425 := by
  unfold tailWord_5961857
  simp only [CollatzResearch.WordTrace]
  refine ⟨217446788762217767957339825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144964525841478511971559883 217446788762217767957339825)
  ·
    refine ⟨163085091571663325968004869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217446788762217767957339825 163085091571663325968004869)
    ·
      refine ⟨30578454669686873619000913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163085091571663325968004869 30578454669686873619000913)
      ·
        refine ⟨22933841002265155214250685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30578454669686873619000913 22933841002265155214250685)
        ·
          refine ⟨8600190375849433205344007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22933841002265155214250685 8600190375849433205344007)
          ·
            refine ⟨12900285563774149808016011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600190375849433205344007 12900285563774149808016011)
            ·
              refine ⟨19350428345661224712024017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12900285563774149808016011 19350428345661224712024017)
              ·
                refine ⟨14512821259245918534018013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19350428345661224712024017 14512821259245918534018013)
                ·
                  refine ⟨5442307972217219450256755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14512821259245918534018013 5442307972217219450256755)
                  ·
                    refine ⟨8163461958325829175385133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442307972217219450256755 8163461958325829175385133)
                    ·
                      refine ⟨3061298234372185940769425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163461958325829175385133 3061298234372185940769425)
                      ·
                        rfl

theorem cell23_5961857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5961857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961857 prefixEnd_5961857 := by exact prefixLift 5961857
  have htrace : WordTrace (prefixWord ++ tailWord_5961857) baseStart_5961857 baseEnd_5961857 := by
    simpa [prefixWord, tailWord_5961857, baseEnd_5961857] using wordTrace_append hprefix tailTrace_5961857
  have hstable : (prefixWord ++ tailWord_5961857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961857).length < 2 ^ (prefixWord ++ tailWord_5961857).sum := by decide
  have hdescent : baseEnd_5961857 < baseStart_5961857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961863 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_5961863 : Nat := 118140960795 + 5961863 * 2 ^ 59
def prefixEnd_5961863 : Nat := 4983230072969 + 3 ^ 40 * 5961863 * 2
def baseEnd_5961863 : Nat := 3061301315256112917294397

theorem tailTrace_5961863 : CollatzResearch.WordTrace tailWord_5961863 prefixEnd_5961863 3061301315256112917294397 := by
  unfold tailWord_5961863
  simp only [CollatzResearch.WordTrace]
  refine ⟨217447007600196030982058243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144964671733464020654705495 217447007600196030982058243)
  ·
    refine ⟨326170511400294046473087365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217447007600196030982058243 326170511400294046473087365)
    ·
      refine ⟨61156970887555133713703881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326170511400294046473087365 61156970887555133713703881)
      ·
        refine ⟨45867728165666350285277911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61156970887555133713703881 45867728165666350285277911)
        ·
          refine ⟨68801592248499525427916867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45867728165666350285277911 68801592248499525427916867)
          ·
            refine ⟨103202388372749288141875301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68801592248499525427916867 103202388372749288141875301)
            ·
              refine ⟨19350447819890491526601619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103202388372749288141875301 19350447819890491526601619)
              ·
                refine ⟨29025671729835737289902429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19350447819890491526601619 29025671729835737289902429)
                ·
                  refine ⟨10884626898688401483713411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29025671729835737289902429 10884626898688401483713411)
                  ·
                    refine ⟨16326940348032602225570117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10884626898688401483713411 16326940348032602225570117)
                    ·
                      refine ⟨3061301315256112917294397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16326940348032602225570117 3061301315256112917294397)
                      ·
                        rfl

theorem cell23_5961863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_5961863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961863 prefixEnd_5961863 := by exact prefixLift 5961863
  have htrace : WordTrace (prefixWord ++ tailWord_5961863) baseStart_5961863 baseEnd_5961863 := by
    simpa [prefixWord, tailWord_5961863, baseEnd_5961863] using wordTrace_append hprefix tailTrace_5961863
  have hstable : (prefixWord ++ tailWord_5961863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961863).length < 2 ^ (prefixWord ++ tailWord_5961863).sum := by decide
  have hdescent : baseEnd_5961863 < baseStart_5961863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961874 : List Nat := [3, 2, 3, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5961874 : Nat := 118140960795 + 5961874 * 2 ^ 59
def prefixEnd_5961874 : Nat := 4983230072969 + 3 ^ 40 * 5961874 * 2
def baseEnd_5961874 : Nat := 3061306963543312374256847

theorem tailTrace_5961874 : CollatzResearch.WordTrace tailWord_5961874 prefixEnd_5961874 3061306963543312374256847 := by
  unfold tailWord_5961874
  simp only [CollatzResearch.WordTrace]
  refine ⟨54361852200789044965177169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144964939202104119907139117 54361852200789044965177169)
  ·
    refine ⟨40771389150591783723882877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54361852200789044965177169 40771389150591783723882877)
    ·
      refine ⟨15289270931471918896456079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40771389150591783723882877 15289270931471918896456079)
      ·
        refine ⟨22933906397207878344684119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15289270931471918896456079 22933906397207878344684119)
        ·
          refine ⟨34400859595811817517026179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22933906397207878344684119 34400859595811817517026179)
          ·
            refine ⟨51601289393717726275539269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34400859595811817517026179 51601289393717726275539269)
            ·
              refine ⟨9675241761322073676663613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51601289393717726275539269 9675241761322073676663613)
              ·
                refine ⟨3628215660495777628748855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9675241761322073676663613 3628215660495777628748855)
                ·
                  refine ⟨5442323490743666443123283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628215660495777628748855 5442323490743666443123283)
                  ·
                    refine ⟨8163485236115499664684925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442323490743666443123283 8163485236115499664684925)
                    ·
                      refine ⟨3061306963543312374256847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163485236115499664684925 3061306963543312374256847)
                      ·
                        rfl

theorem cell23_5961874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5961874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961874 prefixEnd_5961874 := by exact prefixLift 5961874
  have htrace : WordTrace (prefixWord ++ tailWord_5961874) baseStart_5961874 baseEnd_5961874 := by
    simpa [prefixWord, tailWord_5961874, baseEnd_5961874] using wordTrace_append hprefix tailTrace_5961874
  have hstable : (prefixWord ++ tailWord_5961874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961874).length < 2 ^ (prefixWord ++ tailWord_5961874).sum := by decide
  have hdescent : baseEnd_5961874 < baseStart_5961874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961920 : List Nat := [2, 1, 1, 2, 5, 3, 2, 7]
def baseStart_5961920 : Nat := 118140960795 + 5961920 * 2 ^ 59
def prefixEnd_5961920 : Nat := 4983230072969 + 3 ^ 40 * 5961920 * 2
def baseEnd_5961920 : Nat := 113382614209385896084505

theorem tailTrace_5961920 : CollatzResearch.WordTrace tailWord_5961920 prefixEnd_5961920 113382614209385896084505 := by
  unfold tailWord_5961920
  simp only [CollatzResearch.WordTrace]
  refine ⟨108724543280494764858441607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144966057707326353144588809 108724543280494764858441607)
  ·
    refine ⟨163086814920742147287662411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108724543280494764858441607 163086814920742147287662411)
    ·
      refine ⟨244630222381113220931493617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163086814920742147287662411 244630222381113220931493617)
      ·
        refine ⟨183472666785834915698620213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244630222381113220931493617 183472666785834915698620213)
        ·
          refine ⟨17200562511172023346745645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183472666785834915698620213 17200562511172023346745645)
          ·
            refine ⟨6450210941689508755029617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17200562511172023346745645 6450210941689508755029617)
            ·
              refine ⟨4837658206267131566272213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6450210941689508755029617 4837658206267131566272213)
              ·
                refine ⟨113382614209385896084505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4837658206267131566272213 113382614209385896084505)
                ·
                  rfl

theorem cell23_5961920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 7].length) (baseStart_5961920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961920 prefixEnd_5961920 := by exact prefixLift 5961920
  have htrace : WordTrace (prefixWord ++ tailWord_5961920) baseStart_5961920 baseEnd_5961920 := by
    simpa [prefixWord, tailWord_5961920, baseEnd_5961920] using wordTrace_append hprefix tailTrace_5961920
  have hstable : (prefixWord ++ tailWord_5961920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961920).length < 2 ^ (prefixWord ++ tailWord_5961920).sum := by decide
  have hdescent : baseEnd_5961920 < baseStart_5961920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961930 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_5961930 : Nat := 118140960795 + 5961930 * 2 ^ 59
def prefixEnd_5961930 : Nat := 4983230072969 + 3 ^ 40 * 5961930 * 2
def baseEnd_5961930 : Nat := 3061335718459964155156589

theorem tailTrace_5961930 : CollatzResearch.WordTrace tailWord_5961930 prefixEnd_5961930 3061335718459964155156589 := by
  unfold tailWord_5961930
  simp only [CollatzResearch.WordTrace]
  refine ⟨54362362822738325356186811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144966300860635534283164829 54362362822738325356186811)
  ·
    refine ⟨81543544234107488034280217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54362362822738325356186811 81543544234107488034280217)
    ·
      refine ⟨61157658175580616025710163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81543544234107488034280217 61157658175580616025710163)
      ·
        refine ⟨91736487263370924038565245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61157658175580616025710163 91736487263370924038565245)
        ·
          refine ⟨34401182723764096514461967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91736487263370924038565245 34401182723764096514461967)
          ·
            refine ⟨51601774085646144771692951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34401182723764096514461967 51601774085646144771692951)
            ·
              refine ⟨77402661128469217157539427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51601774085646144771692951 77402661128469217157539427)
              ·
                refine ⟨116103991692703825736309141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77402661128469217157539427 116103991692703825736309141)
                ·
                  refine ⟨5442374610595491831389491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116103991692703825736309141 5442374610595491831389491)
                  ·
                    refine ⟨8163561915893237747084237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442374610595491831389491 8163561915893237747084237)
                    ·
                      refine ⟨3061335718459964155156589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163561915893237747084237 3061335718459964155156589)
                      ·
                        rfl

theorem cell23_5961930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_5961930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961930 prefixEnd_5961930 := by exact prefixLift 5961930
  have htrace : WordTrace (prefixWord ++ tailWord_5961930) baseStart_5961930 baseEnd_5961930 := by
    simpa [prefixWord, tailWord_5961930, baseEnd_5961930] using wordTrace_append hprefix tailTrace_5961930
  have hstable : (prefixWord ++ tailWord_5961930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961930).length < 2 ^ (prefixWord ++ tailWord_5961930).sum := by decide
  have hdescent : baseEnd_5961930 < baseStart_5961930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961936 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_5961936 : Nat := 118140960795 + 5961936 * 2 ^ 59
def prefixEnd_5961936 : Nat := 4983230072969 + 3 ^ 40 * 5961936 * 2
def baseEnd_5961936 : Nat := 3061338799343891131681561

theorem tailTrace_5961936 : CollatzResearch.WordTrace tailWord_5961936 prefixEnd_5961936 3061338799343891131681561 := by
  unfold tailWord_5961936
  simp only [CollatzResearch.WordTrace]
  refine ⟨108724835064465782224732831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144966446752621042966310441 108724835064465782224732831)
  ·
    refine ⟨163087252596698673337099247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108724835064465782224732831 163087252596698673337099247)
    ·
      refine ⟨244630878895048010005648871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163087252596698673337099247 244630878895048010005648871)
      ·
        refine ⟨366946318342572015008473307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244630878895048010005648871 366946318342572015008473307)
        ·
          refine ⟨550419477513858022512709961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366946318342572015008473307 550419477513858022512709961)
          ·
            refine ⟨412814608135393516884532471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550419477513858022512709961 412814608135393516884532471)
            ·
              refine ⟨619221912203090275326798707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412814608135393516884532471 619221912203090275326798707)
              ·
                refine ⟨928832868304635412990198061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619221912203090275326798707 928832868304635412990198061)
                ·
                  refine ⟨348312325614238279871324273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928832868304635412990198061 348312325614238279871324273)
                  ·
                    refine ⟨261234244210678709903493205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 348312325614238279871324273 261234244210678709903493205)
                    ·
                      refine ⟨3061338799343891131681561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 261234244210678709903493205 3061338799343891131681561)
                      ·
                        rfl

theorem cell23_5961936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_5961936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961936 prefixEnd_5961936 := by exact prefixLift 5961936
  have htrace : WordTrace (prefixWord ++ tailWord_5961936) baseStart_5961936 baseEnd_5961936 := by
    simpa [prefixWord, tailWord_5961936, baseEnd_5961936] using wordTrace_append hprefix tailTrace_5961936
  have hstable : (prefixWord ++ tailWord_5961936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961936).length < 2 ^ (prefixWord ++ tailWord_5961936).sum := by decide
  have hdescent : baseEnd_5961936 < baseStart_5961936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961948 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5961948 : Nat := 118140960795 + 5961948 * 2 ^ 59
def prefixEnd_5961948 : Nat := 4983230072969 + 3 ^ 40 * 5961948 * 2
def baseEnd_5961948 : Nat := 3061344961111745084731507

theorem tailTrace_5961948 : CollatzResearch.WordTrace tailWord_5961948 prefixEnd_5961948 3061344961111745084731507 := by
  unfold tailWord_5961948
  simp only [CollatzResearch.WordTrace]
  refine ⟨108725053902444045249451249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144966738536592060332601665 108725053902444045249451249)
  ·
    refine ⟨81543790426833033937088437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108725053902444045249451249 81543790426833033937088437)
    ·
      refine ⟨7644730352515596931602041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81543790426833033937088437 7644730352515596931602041)
      ·
        refine ⟨5733547764386697698701531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7644730352515596931602041 5733547764386697698701531)
        ·
          refine ⟨8600321646580046548052297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733547764386697698701531 8600321646580046548052297)
          ·
            refine ⟨6450241234935034911039223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8600321646580046548052297 6450241234935034911039223)
            ·
              refine ⟨9675361852402552366558835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450241234935034911039223 9675361852402552366558835)
              ·
                refine ⟨14513042778603828549838253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9675361852402552366558835 14513042778603828549838253)
                ·
                  refine ⟨5442391041976435706189345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14513042778603828549838253 5442391041976435706189345)
                  ·
                    refine ⟨4081793281482326779642009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5442391041976435706189345 4081793281482326779642009)
                    ·
                      refine ⟨3061344961111745084731507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081793281482326779642009 3061344961111745084731507)
                      ·
                        rfl

theorem cell23_5961948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5961948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961948 prefixEnd_5961948 := by exact prefixLift 5961948
  have htrace : WordTrace (prefixWord ++ tailWord_5961948) baseStart_5961948 baseEnd_5961948 := by
    simpa [prefixWord, tailWord_5961948, baseEnd_5961948] using wordTrace_append hprefix tailTrace_5961948
  have hstable : (prefixWord ++ tailWord_5961948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961948).length < 2 ^ (prefixWord ++ tailWord_5961948).sum := by decide
  have hdescent : baseEnd_5961948 < baseStart_5961948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961953 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_5961953 : Nat := 118140960795 + 5961953 * 2 ^ 59
def prefixEnd_5961953 : Nat := 4983230072969 + 3 ^ 40 * 5961953 * 2
def baseEnd_5961953 : Nat := 3061347528515017565168983

theorem tailTrace_5961953 : CollatzResearch.WordTrace tailWord_5961953 prefixEnd_5961953 3061347528515017565168983 := by
  unfold tailWord_5961953
  simp only [CollatzResearch.WordTrace]
  refine ⟨217450290169869976352834513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144966860113246650901889675 217450290169869976352834513)
  ·
    refine ⟨163087717627402482264625885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217450290169869976352834513 163087717627402482264625885)
    ·
      refine ⟨61157894110275930849234707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163087717627402482264625885 61157894110275930849234707)
      ·
        refine ⟨91736841165413896273852061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61157894110275930849234707 91736841165413896273852061)
        ·
          refine ⟨34401315437030211102694523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91736841165413896273852061 34401315437030211102694523)
          ·
            refine ⟨51601973155545316654041785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34401315437030211102694523 51601973155545316654041785)
            ·
              refine ⟨38701479866658987490531339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51601973155545316654041785 38701479866658987490531339)
              ·
                refine ⟨58052219799988481235797009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38701479866658987490531339 58052219799988481235797009)
                ·
                  refine ⟨43539164849991360926847757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58052219799988481235797009 43539164849991360926847757)
                  ·
                    refine ⟨16327186818746760347567909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43539164849991360926847757 16327186818746760347567909)
                    ·
                      refine ⟨3061347528515017565168983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16327186818746760347567909 3061347528515017565168983)
                      ·
                        rfl

theorem cell23_5961953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_5961953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961953 prefixEnd_5961953 := by exact prefixLift 5961953
  have htrace : WordTrace (prefixWord ++ tailWord_5961953) baseStart_5961953 baseEnd_5961953 := by
    simpa [prefixWord, tailWord_5961953, baseEnd_5961953] using wordTrace_append hprefix tailTrace_5961953
  have hstable : (prefixWord ++ tailWord_5961953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961953).length < 2 ^ (prefixWord ++ tailWord_5961953).sum := by decide
  have hdescent : baseEnd_5961953 < baseStart_5961953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961954 : List Nat := [3, 3, 4, 1, 1, 1, 2, 8]
def baseStart_5961954 : Nat := 118140960795 + 5961954 * 2 ^ 59
def prefixEnd_5961954 : Nat := 4983230072969 + 3 ^ 40 * 5961954 * 2
def baseEnd_5961954 : Nat := 113383260814654520787277

theorem tailTrace_5961954 : CollatzResearch.WordTrace tailWord_5961954 prefixEnd_5961954 113383260814654520787277 := by
  unfold tailWord_5961954
  simp only [CollatzResearch.WordTrace]
  refine ⟨54362581660716588380905229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144966884428577569015747277 54362581660716588380905229)
  ·
    refine ⟨20385968122768720642839461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54362581660716588380905229 20385968122768720642839461)
    ·
      refine ⟨3822369023019135120532399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20385968122768720642839461 3822369023019135120532399)
      ·
        refine ⟨5733553534528702680798599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822369023019135120532399 5733553534528702680798599)
        ·
          refine ⟨8600330301793054021197899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733553534528702680798599 8600330301793054021197899)
          ·
            refine ⟨12900495452689581031796849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600330301793054021197899 12900495452689581031796849)
            ·
              refine ⟨9675371589517185773847637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12900495452689581031796849 9675371589517185773847637)
              ·
                refine ⟨113383260814654520787277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9675371589517185773847637 113383260814654520787277)
                ·
                  rfl

theorem cell23_5961954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 8].length) (baseStart_5961954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961954 prefixEnd_5961954 := by exact prefixLift 5961954
  have htrace : WordTrace (prefixWord ++ tailWord_5961954) baseStart_5961954 baseEnd_5961954 := by
    simpa [prefixWord, tailWord_5961954, baseEnd_5961954] using wordTrace_append hprefix tailTrace_5961954
  have hstable : (prefixWord ++ tailWord_5961954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961954).length < 2 ^ (prefixWord ++ tailWord_5961954).sum := by decide
  have hdescent : baseEnd_5961954 < baseStart_5961954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5961974 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_5961974 : Nat := 118140960795 + 5961974 * 2 ^ 59
def prefixEnd_5961974 : Nat := 4983230072969 + 3 ^ 40 * 5961974 * 2
def baseEnd_5961974 : Nat := 3061358311608761983006387

theorem tailTrace_5961974 : CollatzResearch.WordTrace tailWord_5961974 prefixEnd_5961974 3061358311608761983006387 := by
  unfold tailWord_5961974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13590691006424618558709311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144967370735195931292899317 13590691006424618558709311)
  ·
    refine ⟨20386036509636927838063967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13590691006424618558709311 20386036509636927838063967)
    ·
      refine ⟨30579054764455391757095951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20386036509636927838063967 30579054764455391757095951)
      ·
        refine ⟨45868582146683087635643927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30579054764455391757095951 45868582146683087635643927)
        ·
          refine ⟨68802873220024631453465891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45868582146683087635643927 68802873220024631453465891)
          ·
            refine ⟨103204309830036947180198837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68802873220024631453465891 103204309830036947180198837)
            ·
              refine ⟨9675404046565963798143641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103204309830036947180198837 9675404046565963798143641)
              ·
                refine ⟨7256553034924472848607731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9675404046565963798143641 7256553034924472848607731)
                ·
                  refine ⟨10884829552386709272911597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256553034924472848607731 10884829552386709272911597)
                  ·
                    refine ⟨4081811082145015977341849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10884829552386709272911597 4081811082145015977341849)
                    ·
                      refine ⟨3061358311608761983006387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081811082145015977341849 3061358311608761983006387)
                      ·
                        rfl

theorem cell23_5961974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_5961974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5961974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5961974 prefixEnd_5961974 := by exact prefixLift 5961974
  have htrace : WordTrace (prefixWord ++ tailWord_5961974) baseStart_5961974 baseEnd_5961974 := by
    simpa [prefixWord, tailWord_5961974, baseEnd_5961974] using wordTrace_append hprefix tailTrace_5961974
  have hstable : (prefixWord ++ tailWord_5961974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5961974).length < 2 ^ (prefixWord ++ tailWord_5961974).sum := by decide
  have hdescent : baseEnd_5961974 < baseStart_5961974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5961974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962003 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 3]
def baseStart_5962003 : Nat := 118140960795 + 5962003 * 2 ^ 59
def prefixEnd_5962003 : Nat := 4983230072969 + 3 ^ 40 * 5962003 * 2
def baseEnd_5962003 : Nat := 3061373202547742369543753

theorem tailTrace_5962003 : CollatzResearch.WordTrace tailWord_5962003 prefixEnd_5962003 3061373202547742369543753 := by
  unfold tailWord_5962003
  simp only [CollatzResearch.WordTrace]
  refine ⟨217452113819688834892154663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144968075879792556594769775 217452113819688834892154663)
  ·
    refine ⟨326178170729533252338231995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217452113819688834892154663 326178170729533252338231995)
    ·
      refine ⟨489267256094299878507347993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326178170729533252338231995 489267256094299878507347993)
      ·
        refine ⟨366950442070724908880510995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489267256094299878507347993 366950442070724908880510995)
        ·
          refine ⟨550425663106087363320766493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366950442070724908880510995 550425663106087363320766493)
          ·
            refine ⟨206409623664782761245287435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 550425663106087363320766493 206409623664782761245287435)
            ·
              refine ⟨309614435497174141867931153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206409623664782761245287435 309614435497174141867931153)
              ·
                refine ⟨232210826622880606400948365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309614435497174141867931153 232210826622880606400948365)
                ·
                  refine ⟨87079059983580227400355637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232210826622880606400948365 87079059983580227400355637)
                  ·
                    refine ⟨8163661873460646318783341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87079059983580227400355637 8163661873460646318783341)
                    ·
                      refine ⟨3061373202547742369543753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163661873460646318783341 3061373202547742369543753)
                      ·
                        rfl

theorem cell23_5962003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_5962003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962003 prefixEnd_5962003 := by exact prefixLift 5962003
  have htrace : WordTrace (prefixWord ++ tailWord_5962003) baseStart_5962003 baseEnd_5962003 := by
    simpa [prefixWord, tailWord_5962003, baseEnd_5962003] using wordTrace_append hprefix tailTrace_5962003
  have hstable : (prefixWord ++ tailWord_5962003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962003).length < 2 ^ (prefixWord ++ tailWord_5962003).sum := by decide
  have hdescent : baseEnd_5962003 < baseStart_5962003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962020 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_5962020 : Nat := 118140960795 + 5962020 * 2 ^ 59
def prefixEnd_5962020 : Nat := 4983230072969 + 3 ^ 40 * 5962020 * 2
def baseEnd_5962020 : Nat := 3061381931718868803031175

theorem tailTrace_5962020 : CollatzResearch.WordTrace tailWord_5962020 prefixEnd_5962020 3061381931718868803031175 := by
  unfold tailWord_5962020
  simp only [CollatzResearch.WordTrace]
  refine ⟨108726366930313623397761757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144968489240418164530349009 108726366930313623397761757)
  ·
    refine ⟨40772387598867608774160659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108726366930313623397761757 40772387598867608774160659)
    ·
      refine ⟨61158581398301413161240989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40772387598867608774160659 61158581398301413161240989)
      ·
        refine ⟨22934468024363029935465371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61158581398301413161240989 22934468024363029935465371)
        ·
          refine ⟨34401702036544544903198057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22934468024363029935465371 34401702036544544903198057)
          ·
            refine ⟨25801276527408408677398543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34401702036544544903198057 25801276527408408677398543)
            ·
              refine ⟨38701914791112613016097815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25801276527408408677398543 38701914791112613016097815)
              ·
                refine ⟨58052872186668919524146723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38701914791112613016097815 58052872186668919524146723)
                ·
                  refine ⟨87079308280003379286220085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58052872186668919524146723 87079308280003379286220085)
                  ·
                    refine ⟨8163685151250316808083133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87079308280003379286220085 8163685151250316808083133)
                    ·
                      refine ⟨3061381931718868803031175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163685151250316808083133 3061381931718868803031175)
                      ·
                        rfl

theorem cell23_5962020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_5962020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962020 prefixEnd_5962020 := by exact prefixLift 5962020
  have htrace : WordTrace (prefixWord ++ tailWord_5962020) baseStart_5962020 baseEnd_5962020 := by
    simpa [prefixWord, tailWord_5962020, baseEnd_5962020] using wordTrace_append hprefix tailTrace_5962020
  have hstable : (prefixWord ++ tailWord_5962020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962020).length < 2 ^ (prefixWord ++ tailWord_5962020).sum := by decide
  have hdescent : baseEnd_5962020 < baseStart_5962020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962040 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 2, 5]
def baseStart_5962040 : Nat := 118140960795 + 5962040 * 2 ^ 59
def prefixEnd_5962040 : Nat := 4983230072969 + 3 ^ 40 * 5962040 * 2
def baseEnd_5962040 : Nat := 1020464067110652908260361

theorem tailTrace_5962040 : CollatzResearch.WordTrace tailWord_5962040 prefixEnd_5962040 1020464067110652908260361 := by
  unfold tailWord_5962040
  simp only [CollatzResearch.WordTrace]
  refine ⟨108726731660277395105625787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144968975547036526807501049 108726731660277395105625787)
  ·
    refine ⟨163090097490416092658438681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108726731660277395105625787 163090097490416092658438681)
    ·
      refine ⟨122317573117812069493829011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163090097490416092658438681 122317573117812069493829011)
      ·
        refine ⟨183476359676718104240743517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122317573117812069493829011 183476359676718104240743517)
        ·
          refine ⟨68803634878769289090278819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183476359676718104240743517 68803634878769289090278819)
          ·
            refine ⟨103205452318153933635418229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68803634878769289090278819 103205452318153933635418229)
            ·
              refine ⟨9675511154826931278320459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103205452318153933635418229 9675511154826931278320459)
              ·
                refine ⟨14513266732240396917480689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9675511154826931278320459 14513266732240396917480689)
                ·
                  refine ⟨10884950049180297688110517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14513266732240396917480689 10884950049180297688110517)
                  ·
                    refine ⟨1020464067110652908260361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10884950049180297688110517 1020464067110652908260361)
                    ·
                      rfl

theorem cell23_5962040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_5962040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962040 prefixEnd_5962040 := by exact prefixLift 5962040
  have htrace : WordTrace (prefixWord ++ tailWord_5962040) baseStart_5962040 baseEnd_5962040 := by
    simpa [prefixWord, tailWord_5962040, baseEnd_5962040] using wordTrace_append hprefix tailTrace_5962040
  have hstable : (prefixWord ++ tailWord_5962040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962040).length < 2 ^ (prefixWord ++ tailWord_5962040).sum := by decide
  have hdescent : baseEnd_5962040 < baseStart_5962040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962060 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5962060 : Nat := 118140960795 + 5962060 * 2 ^ 59
def prefixEnd_5962060 : Nat := 4983230072969 + 3 ^ 40 * 5962060 * 2
def baseEnd_5962060 : Nat := 3061402470945048646530991

theorem tailTrace_5962060 : CollatzResearch.WordTrace tailWord_5962060 prefixEnd_5962060 3061402470945048646530991 := by
  unfold tailWord_5962060
  simp only [CollatzResearch.WordTrace]
  refine ⟨108727096390241166813489817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144969461853654889084653089 108727096390241166813489817)
  ·
    refine ⟨81545322292680875110117363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108727096390241166813489817 81545322292680875110117363)
    ·
      refine ⟨122317983439021312665176045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81545322292680875110117363 122317983439021312665176045)
      ·
        refine ⟨45869243789632992249441017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122317983439021312665176045 45869243789632992249441017)
        ·
          refine ⟨34401932842224744187080763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45869243789632992249441017 34401932842224744187080763)
          ·
            refine ⟨51602899263337116280621145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34401932842224744187080763 51602899263337116280621145)
            ·
              refine ⟨38702174447502837210465859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51602899263337116280621145 38702174447502837210465859)
              ·
                refine ⟨58053261671254255815698789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38702174447502837210465859 58053261671254255815698789)
                ·
                  refine ⟨10884986563360172965443523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58053261671254255815698789 10884986563360172965443523)
                  ·
                    refine ⟨16327479845040259448165285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10884986563360172965443523 16327479845040259448165285)
                    ·
                      refine ⟨3061402470945048646530991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16327479845040259448165285 3061402470945048646530991)
                      ·
                        rfl

theorem cell23_5962060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5962060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962060 prefixEnd_5962060 := by exact prefixLift 5962060
  have htrace : WordTrace (prefixWord ++ tailWord_5962060) baseStart_5962060 baseEnd_5962060 := by
    simpa [prefixWord, tailWord_5962060, baseEnd_5962060] using wordTrace_append hprefix tailTrace_5962060
  have hstable : (prefixWord ++ tailWord_5962060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962060).length < 2 ^ (prefixWord ++ tailWord_5962060).sum := by decide
  have hdescent : baseEnd_5962060 < baseStart_5962060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962073 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_5962073 : Nat := 118140960795 + 5962073 * 2 ^ 59
def prefixEnd_5962073 : Nat := 4983230072969 + 3 ^ 40 * 5962073 * 2
def baseEnd_5962073 : Nat := 3061409146193557095668431

theorem tailTrace_5962073 : CollatzResearch.WordTrace tailWord_5962073 prefixEnd_5962073 3061409146193557095668431 := by
  unfold tailWord_5962073
  simp only [CollatzResearch.WordTrace]
  refine ⟨217454666929435236847202873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144969777952956824564801915 217454666929435236847202873)
  ·
    refine ⟨163091000197076427635402155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217454666929435236847202873 163091000197076427635402155)
    ·
      refine ⟨244636500295614641453103233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163091000197076427635402155 244636500295614641453103233)
      ·
        refine ⟨183477375221710981089827425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244636500295614641453103233 183477375221710981089827425)
        ·
          refine ⟨137608031416283235817370569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183477375221710981089827425 137608031416283235817370569)
          ·
            refine ⟨103206023562212426863027927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137608031416283235817370569 103206023562212426863027927)
            ·
              refine ⟨154809035343318640294541891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103206023562212426863027927 154809035343318640294541891)
              ·
                refine ⟨232213553014977960441812837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154809035343318640294541891 232213553014977960441812837)
                ·
                  refine ⟨43540041190308367582839907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232213553014977960441812837 43540041190308367582839907)
                  ·
                    refine ⟨65310061785462551374259861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43540041190308367582839907 65310061785462551374259861)
                    ·
                      refine ⟨3061409146193557095668431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65310061785462551374259861 3061409146193557095668431)
                      ·
                        rfl

theorem cell23_5962073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_5962073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962073 prefixEnd_5962073 := by exact prefixLift 5962073
  have htrace : WordTrace (prefixWord ++ tailWord_5962073) baseStart_5962073 baseEnd_5962073 := by
    simpa [prefixWord, tailWord_5962073, baseEnd_5962073] using wordTrace_append hprefix tailTrace_5962073
  have hstable : (prefixWord ++ tailWord_5962073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962073).length < 2 ^ (prefixWord ++ tailWord_5962073).sum := by decide
  have hdescent : baseEnd_5962073 < baseStart_5962073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962087 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 3, 4]
def baseStart_5962087 : Nat := 118140960795 + 5962087 * 2 ^ 59
def prefixEnd_5962087 : Nat := 4983230072969 + 3 ^ 40 * 5962087 * 2
def baseEnd_5962087 : Nat := 1020472111640906680297789

theorem tailTrace_5962087 : CollatzResearch.WordTrace tailWord_5962087 prefixEnd_5962087 1020472111640906680297789 := by
  unfold tailWord_5962087
  simp only [CollatzResearch.WordTrace]
  refine ⟨217455177551384517238212515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144970118367589678158808343 217455177551384517238212515)
  ·
    refine ⟨326182766327076775857318773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217455177551384517238212515 326182766327076775857318773)
    ·
      refine ⟨30579634343163447736623635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326182766327076775857318773 30579634343163447736623635)
      ·
        refine ⟨45869451514745171604935453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30579634343163447736623635 45869451514745171604935453)
        ·
          refine ⟨17201044318029439351850795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45869451514745171604935453 17201044318029439351850795)
          ·
            refine ⟨25801566477044159027776193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17201044318029439351850795 25801566477044159027776193)
            ·
              refine ⟨19351174857783119270832145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25801566477044159027776193 19351174857783119270832145)
              ·
                refine ⟨14513381143337339453124109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19351174857783119270832145 14513381143337339453124109)
                ·
                  refine ⟨5442517928751502294921541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14513381143337339453124109 5442517928751502294921541)
                  ·
                    refine ⟨1020472111640906680297789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5442517928751502294921541 1020472111640906680297789)
                    ·
                      rfl

theorem cell23_5962087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_5962087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962087 prefixEnd_5962087 := by exact prefixLift 5962087
  have htrace : WordTrace (prefixWord ++ tailWord_5962087) baseStart_5962087 baseEnd_5962087 := by
    simpa [prefixWord, tailWord_5962087, baseEnd_5962087] using wordTrace_append hprefix tailTrace_5962087
  have hstable : (prefixWord ++ tailWord_5962087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962087).length < 2 ^ (prefixWord ++ tailWord_5962087).sum := by decide
  have hdescent : baseEnd_5962087 < baseStart_5962087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962103 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_5962103 : Nat := 118140960795 + 5962103 * 2 ^ 59
def prefixEnd_5962103 : Nat := 4983230072969 + 3 ^ 40 * 5962103 * 2
def baseEnd_5962103 : Nat := 3061424550613191978293293

theorem tailTrace_5962103 : CollatzResearch.WordTrace tailWord_5962103 prefixEnd_5962103 3061424550613191978293293 := by
  unfold tailWord_5962103
  simp only [CollatzResearch.WordTrace]
  refine ⟨217455761119326551970794963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144970507412884367980529975 217455761119326551970794963)
  ·
    refine ⟨326183641678989827956192445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217455761119326551970794963 326183641678989827956192445)
    ·
      refine ⟨122318865629621185483572167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326183641678989827956192445 122318865629621185483572167)
      ·
        refine ⟨183478298444431778225358251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122318865629621185483572167 183478298444431778225358251)
        ·
          refine ⟨275217447666647667338037377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183478298444431778225358251 275217447666647667338037377)
          ·
            refine ⟨206413085749985750503528033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275217447666647667338037377 206413085749985750503528033)
            ·
              refine ⟨154809814312489312877646025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206413085749985750503528033 154809814312489312877646025)
              ·
                refine ⟨116107360734366984658234519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154809814312489312877646025 116107360734366984658234519)
                ·
                  refine ⟨174161041101550476987351779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116107360734366984658234519 174161041101550476987351779)
                  ·
                    refine ⟨261241561652325715481027669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174161041101550476987351779 261241561652325715481027669)
                    ·
                      refine ⟨3061424550613191978293293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 261241561652325715481027669 3061424550613191978293293)
                      ·
                        rfl

theorem cell23_5962103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_5962103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962103 prefixEnd_5962103 := by exact prefixLift 5962103
  have htrace : WordTrace (prefixWord ++ tailWord_5962103) baseStart_5962103 baseEnd_5962103 := by
    simpa [prefixWord, tailWord_5962103, baseEnd_5962103] using wordTrace_append hprefix tailTrace_5962103
  have hstable : (prefixWord ++ tailWord_5962103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962103).length < 2 ^ (prefixWord ++ tailWord_5962103).sum := by decide
  have hdescent : baseEnd_5962103 < baseStart_5962103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962121 : List Nat := [1, 2, 1, 1, 6, 2, 3, 2, 1, 4]
def baseStart_5962121 : Nat := 118140960795 + 5962121 * 2 ^ 59
def prefixEnd_5962121 : Nat := 4983230072969 + 3 ^ 40 * 5962121 * 2
def baseEnd_5962121 : Nat := 1020477931088324302622737

theorem tailTrace_5962121 : CollatzResearch.WordTrace tailWord_5962121 prefixEnd_5962121 1020477931088324302622737 := by
  unfold tailWord_5962121
  simp only [CollatzResearch.WordTrace]
  refine ⟨217456417633261341044950217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144970945088840894029966811 217456417633261341044950217)
  ·
    refine ⟨163092313224946005783712663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217456417633261341044950217 163092313224946005783712663)
    ·
      refine ⟨244638469837419008675568995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163092313224946005783712663 244638469837419008675568995)
      ·
        refine ⟨366957704756128513013353493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244638469837419008675568995 366957704756128513013353493)
        ·
          refine ⟨17201142410443524047500945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 366957704756128513013353493 17201142410443524047500945)
          ·
            refine ⟨12900856807832643035625709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17201142410443524047500945 12900856807832643035625709)
            ·
              refine ⟨4837821302937241138359641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12900856807832643035625709 4837821302937241138359641)
              ·
                refine ⟨3628365977202930853769731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4837821302937241138359641 3628365977202930853769731)
                ·
                  refine ⟨5442548965804396280654597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628365977202930853769731 5442548965804396280654597)
                  ·
                    refine ⟨1020477931088324302622737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5442548965804396280654597 1020477931088324302622737)
                    ·
                      rfl

theorem cell23_5962121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 4].length) (baseStart_5962121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962121 prefixEnd_5962121 := by exact prefixLift 5962121
  have htrace : WordTrace (prefixWord ++ tailWord_5962121) baseStart_5962121 baseEnd_5962121 := by
    simpa [prefixWord, tailWord_5962121, baseEnd_5962121] using wordTrace_append hprefix tailTrace_5962121
  have hstable : (prefixWord ++ tailWord_5962121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962121).length < 2 ^ (prefixWord ++ tailWord_5962121).sum := by decide
  have hdescent : baseEnd_5962121 < baseStart_5962121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962137 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 4, 3, 2]
def baseStart_5962137 : Nat := 118140960795 + 5962137 * 2 ^ 59
def prefixEnd_5962137 : Nat := 4983230072969 + 3 ^ 40 * 5962137 * 2
def baseEnd_5962137 : Nat := 3061442008955444845268137

theorem tailTrace_5962137 : CollatzResearch.WordTrace tailWord_5962137 prefixEnd_5962137 3061442008955444845268137 := by
  unfold tailWord_5962137
  simp only [CollatzResearch.WordTrace]
  refine ⟨217457001201203375777532665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144971334134135583851688443 217457001201203375777532665)
  ·
    refine ⟨163092750900902531833149499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217457001201203375777532665 163092750900902531833149499)
    ·
      refine ⟨244639126351353797749724249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163092750900902531833149499 244639126351353797749724249)
      ·
        refine ⟨183479344763515348312293187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244639126351353797749724249 183479344763515348312293187)
        ·
          refine ⟨275219017145273022468439781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183479344763515348312293187 275219017145273022468439781)
          ·
            refine ⟨51603565714738691712832459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275219017145273022468439781 51603565714738691712832459)
            ·
              refine ⟨77405348572108037569248689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51603565714738691712832459 77405348572108037569248689)
              ·
                refine ⟨58054011429081028176936517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77405348572108037569248689 58054011429081028176936517)
                ·
                  refine ⟨10885127142952692783175597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58054011429081028176936517 10885127142952692783175597)
                  ·
                    refine ⟨4081922678607259793690849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10885127142952692783175597 4081922678607259793690849)
                    ·
                      refine ⟨3061442008955444845268137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081922678607259793690849 3061442008955444845268137)
                      ·
                        rfl

theorem cell23_5962137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_5962137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962137 prefixEnd_5962137 := by exact prefixLift 5962137
  have htrace : WordTrace (prefixWord ++ tailWord_5962137) baseStart_5962137 baseEnd_5962137 := by
    simpa [prefixWord, tailWord_5962137, baseEnd_5962137] using wordTrace_append hprefix tailTrace_5962137
  have hstable : (prefixWord ++ tailWord_5962137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962137).length < 2 ^ (prefixWord ++ tailWord_5962137).sum := by decide
  have hdescent : baseEnd_5962137 < baseStart_5962137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962147 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 1, 5]
def baseStart_5962147 : Nat := 118140960795 + 5962147 * 2 ^ 59
def prefixEnd_5962147 : Nat := 4983230072969 + 3 ^ 40 * 5962147 * 2
def baseEnd_5962147 : Nat := 1020482381253996602047697

theorem tailTrace_5962147 : CollatzResearch.WordTrace tailWord_5962147 prefixEnd_5962147 1020482381253996602047697 := by
  unfold tailWord_5962147
  simp only [CollatzResearch.WordTrace]
  refine ⟨217457365931167147485396695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144971577287444764990264463 217457365931167147485396695)
  ·
    refine ⟨326186048896750721228095043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217457365931167147485396695 326186048896750721228095043)
    ·
      refine ⟨489279073345126081842142565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326186048896750721228095043 489279073345126081842142565)
      ·
        refine ⟨91739826252211140345401731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 489279073345126081842142565 91739826252211140345401731)
        ·
          refine ⟨137609739378316710518102597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91739826252211140345401731 137609739378316710518102597)
          ·
            refine ⟨25801826133434383222144237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137609739378316710518102597 25801826133434383222144237)
            ·
              refine ⟨9675684800037893708304089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25801826133434383222144237 9675684800037893708304089)
              ·
                refine ⟨7256763600028420281228067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9675684800037893708304089 7256763600028420281228067)
                ·
                  refine ⟨10885145400042630421842101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256763600028420281228067 10885145400042630421842101)
                  ·
                    refine ⟨1020482381253996602047697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10885145400042630421842101 1020482381253996602047697)
                    ·
                      rfl

theorem cell23_5962147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 5].length) (baseStart_5962147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962147 prefixEnd_5962147 := by exact prefixLift 5962147
  have htrace : WordTrace (prefixWord ++ tailWord_5962147) baseStart_5962147 baseEnd_5962147 := by
    simpa [prefixWord, tailWord_5962147, baseEnd_5962147] using wordTrace_append hprefix tailTrace_5962147
  have hstable : (prefixWord ++ tailWord_5962147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962147).length < 2 ^ (prefixWord ++ tailWord_5962147).sum := by decide
  have hdescent : baseEnd_5962147 < baseStart_5962147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962197 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5962197 : Nat := 118140960795 + 5962197 * 2 ^ 59
def prefixEnd_5962197 : Nat := 4983230072969 + 3 ^ 40 * 5962197 * 2
def baseEnd_5962197 : Nat := 3061472817794714610517861

theorem tailTrace_5962197 : CollatzResearch.WordTrace tailWord_5962197 prefixEnd_5962197 3061472817794714610517861 := by
  unfold tailWord_5962197
  simp only [CollatzResearch.WordTrace]
  refine ⟨217459189580986006024716845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144972793053990670683144563 217459189580986006024716845)
  ·
    refine ⟨81547196092869752259268817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217459189580986006024716845 81547196092869752259268817)
    ·
      refine ⟨61160397069652314194451613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81547196092869752259268817 61160397069652314194451613)
      ·
        refine ⟨22935148901119617822919355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61160397069652314194451613 22935148901119617822919355)
        ·
          refine ⟨34402723351679426734379033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22935148901119617822919355 34402723351679426734379033)
          ·
            refine ⟨25802042513759570050784275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34402723351679426734379033 25802042513759570050784275)
            ·
              refine ⟨38703063770639355076176413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25802042513759570050784275 38703063770639355076176413)
              ·
                refine ⟨14513648913989758153566155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38703063770639355076176413 14513648913989758153566155)
                ·
                  refine ⟨21770473370984637230349233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14513648913989758153566155 21770473370984637230349233)
                  ·
                    refine ⟨16327855028238477922761925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21770473370984637230349233 16327855028238477922761925)
                    ·
                      refine ⟨3061472817794714610517861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16327855028238477922761925 3061472817794714610517861)
                      ·
                        rfl

theorem cell23_5962197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5962197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962197 prefixEnd_5962197 := by exact prefixLift 5962197
  have htrace : WordTrace (prefixWord ++ tailWord_5962197) baseStart_5962197 baseEnd_5962197 := by
    simpa [prefixWord, tailWord_5962197, baseEnd_5962197] using wordTrace_append hprefix tailTrace_5962197
  have hstable : (prefixWord ++ tailWord_5962197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962197).length < 2 ^ (prefixWord ++ tailWord_5962197).sum := by decide
  have hdescent : baseEnd_5962197 < baseStart_5962197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962207 : List Nat := [1, 1, 2, 3, 3, 3, 3, 7]
def baseStart_5962207 : Nat := 118140960795 + 5962207 * 2 ^ 59
def prefixEnd_5962207 : Nat := 4983230072969 + 3 ^ 40 * 5962207 * 2
def baseEnd_5962207 : Nat := 113388072318565169310845

theorem tailTrace_5962207 : CollatzResearch.WordTrace tailWord_5962207 prefixEnd_5962207 113388072318565169310845 := by
  unfold tailWord_5962207
  simp only [CollatzResearch.WordTrace]
  refine ⟨217459554310949777732580875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144973036207299851821720583 217459554310949777732580875)
  ·
    refine ⟨326189331466424666598871313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217459554310949777732580875 326189331466424666598871313)
    ·
      refine ⟨244641998599818499949153485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326189331466424666598871313 244641998599818499949153485)
      ·
        refine ⟨91740749474931937480932557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244641998599818499949153485 91740749474931937480932557)
        ·
          refine ⟨34402781053099476555349709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91740749474931937480932557 34402781053099476555349709)
          ·
            refine ⟨12901042894912303708256141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34402781053099476555349709 12901042894912303708256141)
            ·
              refine ⟨4837891085592113890596053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12901042894912303708256141 4837891085592113890596053)
              ·
                refine ⟨113388072318565169310845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4837891085592113890596053 113388072318565169310845)
                ·
                  rfl

theorem cell23_5962207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 7].length) (baseStart_5962207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962207 prefixEnd_5962207 := by exact prefixLift 5962207
  have htrace : WordTrace (prefixWord ++ tailWord_5962207) baseStart_5962207 baseEnd_5962207 := by
    simpa [prefixWord, tailWord_5962207, baseEnd_5962207] using wordTrace_append hprefix tailTrace_5962207
  have hstable : (prefixWord ++ tailWord_5962207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962207).length < 2 ^ (prefixWord ++ tailWord_5962207).sum := by decide
  have hdescent : baseEnd_5962207 < baseStart_5962207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962218 : List Nat := [3, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_5962218 : Nat := 118140960795 + 5962218 * 2 ^ 59
def prefixEnd_5962218 : Nat := 4983230072969 + 3 ^ 40 * 5962218 * 2
def baseEnd_5962218 : Nat := 3061483600888459028355265

theorem tailTrace_5962218 : CollatzResearch.WordTrace tailWord_5962218 prefixEnd_5962218 3061483600888459028355265 := by
  unfold tailWord_5962218
  simp only [CollatzResearch.WordTrace]
  refine ⟨54364988878477481652807827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144973303675939951074154205 54364988878477481652807827)
  ·
    refine ⟨81547483317716222479211741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54364988878477481652807827 81547483317716222479211741)
    ·
      refine ⟨30580306244143583429704403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81547483317716222479211741 30580306244143583429704403)
      ·
        refine ⟨45870459366215375144556605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30580306244143583429704403 45870459366215375144556605)
        ·
          refine ⟨17201422262330765679208727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45870459366215375144556605 17201422262330765679208727)
          ·
            refine ⟨25802133393496148518813091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17201422262330765679208727 25802133393496148518813091)
            ·
              refine ⟨38703200090244222778219637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25802133393496148518813091 38703200090244222778219637)
              ·
                refine ⟨3628425008460395885458091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38703200090244222778219637 3628425008460395885458091)
                ·
                  refine ⟨5442637512690593828187137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628425008460395885458091 5442637512690593828187137)
                  ·
                    refine ⟨4081978134517945371140353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5442637512690593828187137 4081978134517945371140353)
                    ·
                      refine ⟨3061483600888459028355265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4081978134517945371140353 3061483600888459028355265)
                      ·
                        rfl

theorem cell23_5962218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_5962218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962218 prefixEnd_5962218 := by exact prefixLift 5962218
  have htrace : WordTrace (prefixWord ++ tailWord_5962218) baseStart_5962218 baseEnd_5962218 := by
    simpa [prefixWord, tailWord_5962218, baseEnd_5962218] using wordTrace_append hprefix tailTrace_5962218
  have hstable : (prefixWord ++ tailWord_5962218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962218).length < 2 ^ (prefixWord ++ tailWord_5962218).sum := by decide
  have hdescent : baseEnd_5962218 < baseStart_5962218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962221 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5962221 : Nat := 118140960795 + 5962221 * 2 ^ 59
def prefixEnd_5962221 : Nat := 4983230072969 + 3 ^ 40 * 5962221 * 2
def baseEnd_5962221 : Nat := 3061485141330422516617751

theorem tailTrace_5962221 : CollatzResearch.WordTrace tailWord_5962221 prefixEnd_5962221 3061485141330422516617751 := by
  unfold tailWord_5962221
  simp only [CollatzResearch.WordTrace]
  refine ⟨217460064932899058123590517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144973376621932705415727011 217460064932899058123590517)
  ·
    refine ⟨20386881087459286699086611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217460064932899058123590517 20386881087459286699086611)
    ·
      refine ⟨30580321631188930048629917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20386881087459286699086611 30580321631188930048629917)
      ·
        refine ⟨11467620611695848768236219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30580321631188930048629917 11467620611695848768236219)
        ·
          refine ⟨17201430917543773152354329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11467620611695848768236219 17201430917543773152354329)
          ·
            refine ⟨12901073188157829864265747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17201430917543773152354329 12901073188157829864265747)
            ·
              refine ⟨19351609782236744796398621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12901073188157829864265747 19351609782236744796398621)
              ·
                refine ⟨7256853668338779298649483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19351609782236744796398621 7256853668338779298649483)
                ·
                  refine ⟨10885280502508168947974225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256853668338779298649483 10885280502508168947974225)
                  ·
                    refine ⟨8163960376881126710980669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10885280502508168947974225 8163960376881126710980669)
                    ·
                      refine ⟨3061485141330422516617751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163960376881126710980669 3061485141330422516617751)
                      ·
                        rfl

theorem cell23_5962221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5962221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962221 prefixEnd_5962221 := by exact prefixLift 5962221
  have htrace : WordTrace (prefixWord ++ tailWord_5962221) baseStart_5962221 baseEnd_5962221 := by
    simpa [prefixWord, tailWord_5962221, baseEnd_5962221] using wordTrace_append hprefix tailTrace_5962221
  have hstable : (prefixWord ++ tailWord_5962221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962221).length < 2 ^ (prefixWord ++ tailWord_5962221).sum := by decide
  have hdescent : baseEnd_5962221 < baseStart_5962221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962234 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_5962234 : Nat := 118140960795 + 5962234 * 2 ^ 59
def prefixEnd_5962234 : Nat := 4983230072969 + 3 ^ 40 * 5962234 * 2
def baseEnd_5962234 : Nat := 3061491816578930965755191

theorem tailTrace_5962234 : CollatzResearch.WordTrace tailWord_5962234 prefixEnd_5962234 3061491816578930965755191 := by
  unfold tailWord_5962234
  simp only [CollatzResearch.WordTrace]
  refine ⟨54365134770462990335953439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144973692721234640895875837 54365134770462990335953439)
  ·
    refine ⟨81547702155694485503930159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54365134770462990335953439 81547702155694485503930159)
    ·
      refine ⟨122321553233541728255895239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81547702155694485503930159 122321553233541728255895239)
      ·
        refine ⟨183482329850312592383842859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122321553233541728255895239 183482329850312592383842859)
        ·
          refine ⟨275223494775468888575764289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183482329850312592383842859 275223494775468888575764289)
          ·
            refine ⟨206417621081601666431823217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275223494775468888575764289 206417621081601666431823217)
            ·
              refine ⟨154813215811201249823867413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206417621081601666431823217 154813215811201249823867413)
              ·
                refine ⟨7256869491150058585493785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154813215811201249823867413 7256869491150058585493785)
                ·
                  refine ⟨5442652118362543939120339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7256869491150058585493785 5442652118362543939120339)
                  ·
                    refine ⟨8163978177543815908680509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442652118362543939120339 8163978177543815908680509)
                    ·
                      refine ⟨3061491816578930965755191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8163978177543815908680509 3061491816578930965755191)
                      ·
                        rfl

theorem cell23_5962234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_5962234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962234 prefixEnd_5962234 := by exact prefixLift 5962234
  have htrace : WordTrace (prefixWord ++ tailWord_5962234) baseStart_5962234 baseEnd_5962234 := by
    simpa [prefixWord, tailWord_5962234, baseEnd_5962234] using wordTrace_append hprefix tailTrace_5962234
  have hstable : (prefixWord ++ tailWord_5962234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962234).length < 2 ^ (prefixWord ++ tailWord_5962234).sum := by decide
  have hdescent : baseEnd_5962234 < baseStart_5962234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962261 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_5962261 : Nat := 118140960795 + 5962261 * 2 ^ 59
def prefixEnd_5962261 : Nat := 4983230072969 + 3 ^ 40 * 5962261 * 2
def baseEnd_5962261 : Nat := 3061505680556602360117567

theorem tailTrace_5962261 : CollatzResearch.WordTrace tailWord_5962261 prefixEnd_5962261 3061505680556602360117567 := by
  unfold tailWord_5962261
  simp only [CollatzResearch.WordTrace]
  refine ⟨217461523852754144955046637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144974349235169429970031091 217461523852754144955046637)
  ·
    refine ⟨81548071444782804358142489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217461523852754144955046637 81548071444782804358142489)
    ·
      refine ⟨61161053583587103268606867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81548071444782804358142489 61161053583587103268606867)
      ·
        refine ⟨91741580375380654902910301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61161053583587103268606867 91741580375380654902910301)
        ·
          refine ⟨34403092640767745588591363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91741580375380654902910301 34403092640767745588591363)
          ·
            refine ⟨51604638961151618382887045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34403092640767745588591363 51604638961151618382887045)
            ·
              refine ⟨9675869805215928446791321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51604638961151618382887045 9675869805215928446791321)
              ·
                refine ⟨7256902353911946335093491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9675869805215928446791321 7256902353911946335093491)
                ·
                  refine ⟨10885353530867919502640237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7256902353911946335093491 10885353530867919502640237)
                  ·
                    refine ⟨4082007574075469813490089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10885353530867919502640237 4082007574075469813490089)
                    ·
                      refine ⟨3061505680556602360117567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082007574075469813490089 3061505680556602360117567)
                      ·
                        rfl

theorem cell23_5962261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_5962261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962261 prefixEnd_5962261 := by exact prefixLift 5962261
  have htrace : WordTrace (prefixWord ++ tailWord_5962261) baseStart_5962261 baseEnd_5962261 := by
    simpa [prefixWord, tailWord_5962261, baseEnd_5962261] using wordTrace_append hprefix tailTrace_5962261
  have hstable : (prefixWord ++ tailWord_5962261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962261).length < 2 ^ (prefixWord ++ tailWord_5962261).sum := by decide
  have hdescent : baseEnd_5962261 < baseStart_5962261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962274 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_5962274 : Nat := 118140960795 + 5962274 * 2 ^ 59
def prefixEnd_5962274 : Nat := 4983230072969 + 3 ^ 40 * 5962274 * 2
def baseEnd_5962274 : Nat := 3061512355805110809255007

theorem tailTrace_5962274 : CollatzResearch.WordTrace tailWord_5962274 prefixEnd_5962274 3061512355805110809255007 := by
  unfold tailWord_5962274
  simp only [CollatzResearch.WordTrace]
  refine ⟨54365499500426762043817469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144974665334471365450179917 54365499500426762043817469)
  ·
    refine ⟨20387062312660035766431551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54365499500426762043817469 20387062312660035766431551)
    ·
      refine ⟨30580593468990053649647327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20387062312660035766431551 30580593468990053649647327)
      ·
        refine ⟨45870890203485080474470991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30580593468990053649647327 45870890203485080474470991)
        ·
          refine ⟨68806335305227620711706487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45870890203485080474470991 68806335305227620711706487)
          ·
            refine ⟨103209502957841431067559731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68806335305227620711706487 103209502957841431067559731)
            ·
              refine ⟨154814254436762146601339597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103209502957841431067559731 154814254436762146601339597)
              ·
                refine ⟨58055345413785804975502349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154814254436762146601339597 58055345413785804975502349)
                ·
                  refine ⟨21770754530169676865813381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58055345413785804975502349 21770754530169676865813381)
                  ·
                    refine ⟨4082016474406814412340009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21770754530169676865813381 4082016474406814412340009)
                    ·
                      refine ⟨3061512355805110809255007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082016474406814412340009 3061512355805110809255007)
                      ·
                        rfl

theorem cell23_5962274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_5962274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962274 prefixEnd_5962274 := by exact prefixLift 5962274
  have htrace : WordTrace (prefixWord ++ tailWord_5962274) baseStart_5962274 baseEnd_5962274 := by
    simpa [prefixWord, tailWord_5962274, baseEnd_5962274] using wordTrace_append hprefix tailTrace_5962274
  have hstable : (prefixWord ++ tailWord_5962274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962274).length < 2 ^ (prefixWord ++ tailWord_5962274).sum := by decide
  have hdescent : baseEnd_5962274 < baseStart_5962274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962291 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 2, 2, 2]
def baseStart_5962291 : Nat := 118140960795 + 5962291 * 2 ^ 59
def prefixEnd_5962291 : Nat := 4983230072969 + 3 ^ 40 * 5962291 * 2
def baseEnd_5962291 : Nat := 3061521084976237242742429

theorem tailTrace_5962291 : CollatzResearch.WordTrace tailWord_5962291 prefixEnd_5962291 3061521084976237242742429 := by
  unfold tailWord_5962291
  simp only [CollatzResearch.WordTrace]
  refine ⟨217462618042645460078638727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144975078695096973385759151 217462618042645460078638727)
  ·
    refine ⟨326193927063968190117958091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217462618042645460078638727 326193927063968190117958091)
    ·
      refine ⟨489290890595952285176937137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326193927063968190117958091 489290890595952285176937137)
      ·
        refine ⟨366968167946964213882702853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489290890595952285176937137 366968167946964213882702853)
        ·
          refine ⟨68806531490055790103006785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 366968167946964213882702853 68806531490055790103006785)
          ·
            refine ⟨51604898617541842577255089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68806531490055790103006785 51604898617541842577255089)
            ·
              refine ⟨38703673963156381932941317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51604898617541842577255089 38703673963156381932941317)
              ·
                refine ⟨7256938868091821612426497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38703673963156381932941317 7256938868091821612426497)
                ·
                  refine ⟨5442704151068866209319873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7256938868091821612426497 5442704151068866209319873)
                  ·
                    refine ⟨4082028113301649656989905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5442704151068866209319873 4082028113301649656989905)
                    ·
                      refine ⟨3061521084976237242742429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082028113301649656989905 3061521084976237242742429)
                      ·
                        rfl

theorem cell23_5962291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 2, 2].length) (baseStart_5962291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962291 prefixEnd_5962291 := by exact prefixLift 5962291
  have htrace : WordTrace (prefixWord ++ tailWord_5962291) baseStart_5962291 baseEnd_5962291 := by
    simpa [prefixWord, tailWord_5962291, baseEnd_5962291] using wordTrace_append hprefix tailTrace_5962291
  have hstable : (prefixWord ++ tailWord_5962291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962291).length < 2 ^ (prefixWord ++ tailWord_5962291).sum := by decide
  have hdescent : baseEnd_5962291 < baseStart_5962291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962302 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5962302 : Nat := 118140960795 + 5962302 * 2 ^ 59
def prefixEnd_5962302 : Nat := 4983230072969 + 3 ^ 40 * 5962302 * 2
def baseEnd_5962302 : Nat := 3061526733263436699704879

theorem tailTrace_5962302 : CollatzResearch.WordTrace tailWord_5962302 prefixEnd_5962302 3061526733263436699704879 := by
  unfold tailWord_5962302
  simp only [CollatzResearch.WordTrace]
  refine ⟨27182877405700701119661145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144975346163737072638192773 27182877405700701119661145)
  ·
    refine ⟨20387158054275525839745859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27182877405700701119661145 20387158054275525839745859)
    ·
      refine ⟨30580737081413288759618789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20387158054275525839745859 30580737081413288759618789)
      ·
        refine ⟨5733888202764991642428523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30580737081413288759618789 5733888202764991642428523)
        ·
          refine ⟨8600832304147487463642785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5733888202764991642428523 8600832304147487463642785)
          ·
            refine ⟨6450624228110615597732089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8600832304147487463642785 6450624228110615597732089)
            ·
              refine ⟨4837968171082961698299067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6450624228110615597732089 4837968171082961698299067)
              ·
                refine ⟨7256952256624442547448601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4837968171082961698299067 7256952256624442547448601)
                ·
                  refine ⟨5442714192468331910586451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7256952256624442547448601 5442714192468331910586451)
                  ·
                    refine ⟨8164071288702497865879677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442714192468331910586451 8164071288702497865879677)
                    ·
                      refine ⟨3061526733263436699704879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8164071288702497865879677 3061526733263436699704879)
                      ·
                        rfl

theorem cell23_5962302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5962302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962302 prefixEnd_5962302 := by exact prefixLift 5962302
  have htrace : WordTrace (prefixWord ++ tailWord_5962302) baseStart_5962302 baseEnd_5962302 := by
    simpa [prefixWord, tailWord_5962302, baseEnd_5962302] using wordTrace_append hprefix tailTrace_5962302
  have hstable : (prefixWord ++ tailWord_5962302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962302).length < 2 ^ (prefixWord ++ tailWord_5962302).sum := by decide
  have hdescent : baseEnd_5962302 < baseStart_5962302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962307 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 3]
def baseStart_5962307 : Nat := 118140960795 + 5962307 * 2 ^ 59
def prefixEnd_5962307 : Nat := 4983230072969 + 3 ^ 40 * 5962307 * 2
def baseEnd_5962307 : Nat := 3061529300666709180142355

theorem tailTrace_5962307 : CollatzResearch.WordTrace tailWord_5962307 prefixEnd_5962307 3061529300666709180142355 := by
  unfold tailWord_5962307
  simp only [CollatzResearch.WordTrace]
  refine ⟨217463201610587494811221175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144975467740391663207480783 217463201610587494811221175)
  ·
    refine ⟨326194802415881242216831763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217463201610587494811221175 326194802415881242216831763)
    ·
      refine ⟨489292203623821863325247645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326194802415881242216831763 489292203623821863325247645)
      ·
        refine ⟨183484576358933198746967867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489292203623821863325247645 183484576358933198746967867)
        ·
          refine ⟨275226864538399798120451801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183484576358933198746967867 275226864538399798120451801)
          ·
            refine ⟨206420148403799848590338851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275226864538399798120451801 206420148403799848590338851)
            ·
              refine ⟨309630222605699772885508277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206420148403799848590338851 309630222605699772885508277)
              ·
                refine ⟨29027833369284353708016401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 309630222605699772885508277 29027833369284353708016401)
                ·
                  refine ⟨21770875026963265281012301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29027833369284353708016401 21770875026963265281012301)
                  ·
                    refine ⟨8164078135111224480379613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21770875026963265281012301 8164078135111224480379613)
                    ·
                      refine ⟨3061529300666709180142355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8164078135111224480379613 3061529300666709180142355)
                      ·
                        rfl

theorem cell23_5962307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_5962307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962307 prefixEnd_5962307 := by exact prefixLift 5962307
  have htrace : WordTrace (prefixWord ++ tailWord_5962307) baseStart_5962307 baseEnd_5962307 := by
    simpa [prefixWord, tailWord_5962307, baseEnd_5962307] using wordTrace_append hprefix tailTrace_5962307
  have hstable : (prefixWord ++ tailWord_5962307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962307).length < 2 ^ (prefixWord ++ tailWord_5962307).sum := by decide
  have hdescent : baseEnd_5962307 < baseStart_5962307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962337 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_5962337 : Nat := 118140960795 + 5962337 * 2 ^ 59
def prefixEnd_5962337 : Nat := 4983230072969 + 3 ^ 40 * 5962337 * 2
def baseEnd_5962337 : Nat := 3061544705086344062767217

theorem tailTrace_5962337 : CollatzResearch.WordTrace tailWord_5962337 prefixEnd_5962337 3061544705086344062767217 := by
  unfold tailWord_5962337
  simp only [CollatzResearch.WordTrace]
  refine ⟨217464295800478809934813265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144976197200319206623208843 217464295800478809934813265)
  ·
    refine ⟨163098221850359107451109949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217464295800478809934813265 163098221850359107451109949)
    ·
      refine ⟨61161833193884665294166231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163098221850359107451109949 61161833193884665294166231)
      ·
        refine ⟨91742749790826997941249347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61161833193884665294166231 91742749790826997941249347)
        ·
          refine ⟨137614124686240496911874021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91742749790826997941249347 137614124686240496911874021)
          ·
            refine ⟨25802648378670093170976379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137614124686240496911874021 25802648378670093170976379)
            ·
              refine ⟨38703972568005139756464569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25802648378670093170976379 38703972568005139756464569)
              ·
                refine ⟨29027979426003854817348427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38703972568005139756464569 29027979426003854817348427)
                ·
                  refine ⟨43541969139005782226022641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29027979426003854817348427 43541969139005782226022641)
                  ·
                    refine ⟨32656476854254336669516981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43541969139005782226022641 32656476854254336669516981)
                    ·
                      refine ⟨3061544705086344062767217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32656476854254336669516981 3061544705086344062767217)
                      ·
                        rfl

theorem cell23_5962337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_5962337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962337 prefixEnd_5962337 := by exact prefixLift 5962337
  have htrace : WordTrace (prefixWord ++ tailWord_5962337) baseStart_5962337 baseEnd_5962337 := by
    simpa [prefixWord, tailWord_5962337, baseEnd_5962337] using wordTrace_append hprefix tailTrace_5962337
  have hstable : (prefixWord ++ tailWord_5962337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962337).length < 2 ^ (prefixWord ++ tailWord_5962337).sum := by decide
  have hdescent : baseEnd_5962337 < baseStart_5962337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962347 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 4]
def baseStart_5962347 : Nat := 118140960795 + 5962347 * 2 ^ 59
def prefixEnd_5962347 : Nat := 4983230072969 + 3 ^ 40 * 5962347 * 2
def baseEnd_5962347 : Nat := 3061549839892889023642171

theorem tailTrace_5962347 : CollatzResearch.WordTrace tailWord_5962347 prefixEnd_5962347 3061549839892889023642171 := by
  unfold tailWord_5962347
  simp only [CollatzResearch.WordTrace]
  refine ⟨217464660530442581642677295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144976440353628387761784863 217464660530442581642677295)
  ·
    refine ⟨326196990795663872464015943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217464660530442581642677295 326196990795663872464015943)
    ·
      refine ⟨489295486193495808696023915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326196990795663872464015943 489295486193495808696023915)
      ·
        refine ⟨733943229290243713044035873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489295486193495808696023915 733943229290243713044035873)
        ·
          refine ⟨550457421967682784783026905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733943229290243713044035873 550457421967682784783026905)
          ·
            refine ⟨412843066475762088587270179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550457421967682784783026905 412843066475762088587270179)
            ·
              refine ⟨619264599713643132880905269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412843066475762088587270179 619264599713643132880905269)
              ·
                refine ⟨58056056223154043707584869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 619264599713643132880905269 58056056223154043707584869)
                ·
                  refine ⟨10885510541841383195172163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58056056223154043707584869 10885510541841383195172163)
                  ·
                    refine ⟨16328265812762074792758245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10885510541841383195172163 16328265812762074792758245)
                    ·
                      refine ⟨3061549839892889023642171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16328265812762074792758245 3061549839892889023642171)
                      ·
                        rfl

theorem cell23_5962347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 4].length) (baseStart_5962347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962347 prefixEnd_5962347 := by exact prefixLift 5962347
  have htrace : WordTrace (prefixWord ++ tailWord_5962347) baseStart_5962347 baseEnd_5962347 := by
    simpa [prefixWord, tailWord_5962347, baseEnd_5962347] using wordTrace_append hprefix tailTrace_5962347
  have hstable : (prefixWord ++ tailWord_5962347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962347).length < 2 ^ (prefixWord ++ tailWord_5962347).sum := by decide
  have hdescent : baseEnd_5962347 < baseStart_5962347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962364 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_5962364 : Nat := 118140960795 + 5962364 * 2 ^ 59
def prefixEnd_5962364 : Nat := 4983230072969 + 3 ^ 40 * 5962364 * 2
def baseEnd_5962364 : Nat := 3061558569064015457129593

theorem tailTrace_5962364 : CollatzResearch.WordTrace tailWord_5962364 prefixEnd_5962364 3061558569064015457129593 := by
  unfold tailWord_5962364
  simp only [CollatzResearch.WordTrace]
  refine ⟨108732640285690496773023073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144976853714253995697364097 108732640285690496773023073)
  ·
    refine ⟨81549480214267872579767305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108732640285690496773023073 81549480214267872579767305)
    ·
      refine ⟨61162110160700904434825479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81549480214267872579767305 61162110160700904434825479)
      ·
        refine ⟨91743165241051356652238219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61162110160700904434825479 91743165241051356652238219)
        ·
          refine ⟨137614747861577034978357329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91743165241051356652238219 137614747861577034978357329)
          ·
            refine ⟨103211060896182776233767997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137614747861577034978357329 103211060896182776233767997)
            ·
              refine ⟨38704147836068541087662999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103211060896182776233767997 38704147836068541087662999)
              ·
                refine ⟨58056221754102811631494499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38704147836068541087662999 58056221754102811631494499)
                ·
                  refine ⟨87084332631154217447241749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58056221754102811631494499 87084332631154217447241749)
                  ·
                    refine ⟨4082078092085353942839457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87084332631154217447241749 4082078092085353942839457)
                    ·
                      refine ⟨3061558569064015457129593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082078092085353942839457 3061558569064015457129593)
                      ·
                        rfl

theorem cell23_5962364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_5962364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962364 prefixEnd_5962364 := by exact prefixLift 5962364
  have htrace : WordTrace (prefixWord ++ tailWord_5962364) baseStart_5962364 baseEnd_5962364 := by
    simpa [prefixWord, tailWord_5962364, baseEnd_5962364] using wordTrace_append hprefix tailTrace_5962364
  have hstable : (prefixWord ++ tailWord_5962364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962364).length < 2 ^ (prefixWord ++ tailWord_5962364).sum := by decide
  have hdescent : baseEnd_5962364 < baseStart_5962364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962378 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_5962378 : Nat := 118140960795 + 5962378 * 2 ^ 59
def prefixEnd_5962378 : Nat := 4983230072969 + 3 ^ 40 * 5962378 * 2
def baseEnd_5962378 : Nat := 1020521919264392800784843

theorem tailTrace_5962378 : CollatzResearch.WordTrace tailWord_5962378 prefixEnd_5962378 1020521919264392800784843 := by
  unfold tailWord_5962378
  simp only [CollatzResearch.WordTrace]
  refine ⟨54366447798332568484263947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144977194128886849291370525 54366447798332568484263947)
  ·
    refine ⟨81549671697498852726395921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54366447798332568484263947 81549671697498852726395921)
    ·
      refine ⟨61162253773124139544796941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81549671697498852726395921 61162253773124139544796941)
      ·
        refine ⟨22935845164921552329298853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61162253773124139544796941 22935845164921552329298853)
        ·
          refine ⟨4300470968422791061743535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22935845164921552329298853 4300470968422791061743535)
          ·
            refine ⟨6450706452634186592615303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4300470968422791061743535 6450706452634186592615303)
            ·
              refine ⟨9676059678951279888922955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450706452634186592615303 9676059678951279888922955)
              ·
                refine ⟨14514089518426919833384433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676059678951279888922955 14514089518426919833384433)
                ·
                  refine ⟨10885567138820189875038325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14514089518426919833384433 10885567138820189875038325)
                  ·
                    refine ⟨1020521919264392800784843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10885567138820189875038325 1020521919264392800784843)
                    ·
                      rfl

theorem cell23_5962378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_5962378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962378 prefixEnd_5962378 := by exact prefixLift 5962378
  have htrace : WordTrace (prefixWord ++ tailWord_5962378) baseStart_5962378 baseEnd_5962378 := by
    simpa [prefixWord, tailWord_5962378, baseEnd_5962378] using wordTrace_append hprefix tailTrace_5962378
  have hstable : (prefixWord ++ tailWord_5962378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962378).length < 2 ^ (prefixWord ++ tailWord_5962378).sum := by decide
  have hdescent : baseEnd_5962378 < baseStart_5962378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962431 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 3]
def baseStart_5962431 : Nat := 118140960795 + 5962431 * 2 ^ 59
def prefixEnd_5962431 : Nat := 4983230072969 + 3 ^ 40 * 5962431 * 2
def baseEnd_5962431 : Nat := 3061592972267866694991785

theorem tailTrace_5962431 : CollatzResearch.WordTrace tailWord_5962431 prefixEnd_5962431 3061592972267866694991785 := by
  unfold tailWord_5962431
  simp only [CollatzResearch.WordTrace]
  refine ⟨217467724262138263988735147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144978482841425509325823431 217467724262138263988735147)
  ·
    refine ⟨326201586393207395983102721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217467724262138263988735147 326201586393207395983102721)
    ·
      refine ⟨244651189794905546987327041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326201586393207395983102721 244651189794905546987327041)
      ·
        refine ⟨183488392346179160240495281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244651189794905546987327041 183488392346179160240495281)
        ·
          refine ⟨137616294259634370180371461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183488392346179160240495281 137616294259634370180371461)
          ·
            refine ⟨25803055173681444408819649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137616294259634370180371461 25803055173681444408819649)
            ·
              refine ⟨19352291380261083306614737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25803055173681444408819649 19352291380261083306614737)
              ·
                refine ⟨14514218535195812479961053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19352291380261083306614737 14514218535195812479961053)
                ·
                  refine ⟨5442831950698429679985395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14514218535195812479961053 5442831950698429679985395)
                  ·
                    refine ⟨8164247926047644519978093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5442831950698429679985395 8164247926047644519978093)
                    ·
                      refine ⟨3061592972267866694991785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8164247926047644519978093 3061592972267866694991785)
                      ·
                        rfl

theorem cell23_5962431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_5962431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962431 prefixEnd_5962431 := by exact prefixLift 5962431
  have htrace : WordTrace (prefixWord ++ tailWord_5962431) baseStart_5962431 baseEnd_5962431 := by
    simpa [prefixWord, tailWord_5962431, baseEnd_5962431] using wordTrace_append hprefix tailTrace_5962431
  have hstable : (prefixWord ++ tailWord_5962431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962431).length < 2 ^ (prefixWord ++ tailWord_5962431).sum := by decide
  have hdescent : baseEnd_5962431 < baseStart_5962431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962474 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_5962474 : Nat := 118140960795 + 5962474 * 2 ^ 59
def prefixEnd_5962474 : Nat := 4983230072969 + 3 ^ 40 * 5962474 * 2
def baseEnd_5962474 : Nat := 3061615051936010026754087

theorem tailTrace_5962474 : CollatzResearch.WordTrace tailWord_5962474 prefixEnd_5962474 3061615051936010026754087 := by
  unfold tailWord_5962474
  simp only [CollatzResearch.WordTrace]
  refine ⟨54367323150245620583137619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144979528400654988221700317 54367323150245620583137619)
  ·
    refine ⟨81550984725368430874706429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54367323150245620583137619 81550984725368430874706429)
    ·
      refine ⟨30581619272013161578014911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81550984725368430874706429 30581619272013161578014911)
      ·
        refine ⟨45872428908019742367022367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30581619272013161578014911 45872428908019742367022367)
        ·
          refine ⟨68808643362029613550533551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45872428908019742367022367 68808643362029613550533551)
          ·
            refine ⟨103212965043044420325800327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68808643362029613550533551 103212965043044420325800327)
            ·
              refine ⟨154819447564566630488700491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103212965043044420325800327 154819447564566630488700491)
              ·
                refine ⟨232229171346849945733050737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154819447564566630488700491 232229171346849945733050737)
                ·
                  refine ⟨174171878510137459299788053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232229171346849945733050737 174171878510137459299788053)
                  ·
                    refine ⟨8164306805162693404677565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 174171878510137459299788053 8164306805162693404677565)
                    ·
                      refine ⟨3061615051936010026754087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8164306805162693404677565 3061615051936010026754087)
                      ·
                        rfl

theorem cell23_5962474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_5962474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962474 prefixEnd_5962474 := by exact prefixLift 5962474
  have htrace : WordTrace (prefixWord ++ tailWord_5962474) baseStart_5962474 baseEnd_5962474 := by
    simpa [prefixWord, tailWord_5962474, baseEnd_5962474] using wordTrace_append hprefix tailTrace_5962474
  have hstable : (prefixWord ++ tailWord_5962474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962474).length < 2 ^ (prefixWord ++ tailWord_5962474).sum := by decide
  have hdescent : baseEnd_5962474 < baseStart_5962474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962481 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 2, 4]
def baseStart_5962481 : Nat := 118140960795 + 5962481 * 2 ^ 59
def prefixEnd_5962481 : Nat := 4983230072969 + 3 ^ 40 * 5962481 * 2
def baseEnd_5962481 : Nat := 1020539548766863833122185

theorem tailTrace_5962481 : CollatzResearch.WordTrace tailWord_5962481 prefixEnd_5962481 1020539548766863833122185 := by
  unfold tailWord_5962481
  simp only [CollatzResearch.WordTrace]
  refine ⟨217469547911957122528055297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144979698607971415018703531 217469547911957122528055297)
  ·
    refine ⟨163102160933967841896041473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217469547911957122528055297 163102160933967841896041473)
    ·
      refine ⟨122326620700475881422031105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163102160933967841896041473 122326620700475881422031105)
      ·
        refine ⟨91744965525356911066523329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122326620700475881422031105 91744965525356911066523329)
        ·
          refine ⟨68808724144017683299892497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91744965525356911066523329 68808724144017683299892497)
          ·
            refine ⟨51606543108013262474919373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68808724144017683299892497 51606543108013262474919373)
            ·
              refine ⟨19352453665504973428094765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51606543108013262474919373 19352453665504973428094765)
              ·
                refine ⟨7257170124564365035535537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19352453665504973428094765 7257170124564365035535537)
                ·
                  refine ⟨5442877593423273776651653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7257170124564365035535537 5442877593423273776651653)
                  ·
                    refine ⟨1020539548766863833122185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5442877593423273776651653 1020539548766863833122185)
                    ·
                      rfl

theorem cell23_5962481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_5962481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962481 prefixEnd_5962481 := by exact prefixLift 5962481
  have htrace : WordTrace (prefixWord ++ tailWord_5962481) baseStart_5962481 baseEnd_5962481 := by
    simpa [prefixWord, tailWord_5962481, baseEnd_5962481] using wordTrace_append hprefix tailTrace_5962481
  have hstable : (prefixWord ++ tailWord_5962481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962481).length < 2 ^ (prefixWord ++ tailWord_5962481).sum := by decide
  have hdescent : baseEnd_5962481 < baseStart_5962481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962485 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5962485 : Nat := 118140960795 + 5962485 * 2 ^ 59
def prefixEnd_5962485 : Nat := 4983230072969 + 3 ^ 40 * 5962485 * 2
def baseEnd_5962485 : Nat := 1020540233407736494572179

theorem tailTrace_5962485 : CollatzResearch.WordTrace tailWord_5962485 prefixEnd_5962485 1020540233407736494572179 := by
  unfold tailWord_5962485
  simp only [CollatzResearch.WordTrace]
  refine ⟨217469693803942631211200909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144979795869295087474133939 217469693803942631211200909)
  ·
    refine ⟨81551135176478486704200341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217469693803942631211200909 81551135176478486704200341)
    ·
      refine ⟨3822709461397429064259391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81551135176478486704200341 3822709461397429064259391)
      ·
        refine ⟨5734064192096143596389087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3822709461397429064259391 5734064192096143596389087)
        ·
          refine ⟨8601096288144215394583631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5734064192096143596389087 8601096288144215394583631)
          ·
            refine ⟨12901644432216323091875447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8601096288144215394583631 12901644432216323091875447)
            ·
              refine ⟨19352466648324484637813171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12901644432216323091875447 19352466648324484637813171)
              ·
                refine ⟨29028699972486726956719757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19352466648324484637813171 29028699972486726956719757)
                ·
                  refine ⟨10885762489682522608769909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29028699972486726956719757 10885762489682522608769909)
                  ·
                    refine ⟨1020540233407736494572179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10885762489682522608769909 1020540233407736494572179)
                    ·
                      rfl

theorem cell23_5962485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5962485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962485 prefixEnd_5962485 := by exact prefixLift 5962485
  have htrace : WordTrace (prefixWord ++ tailWord_5962485) baseStart_5962485 baseEnd_5962485 := by
    simpa [prefixWord, tailWord_5962485, baseEnd_5962485] using wordTrace_append hprefix tailTrace_5962485
  have hstable : (prefixWord ++ tailWord_5962485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962485).length < 2 ^ (prefixWord ++ tailWord_5962485).sum := by decide
  have hdescent : baseEnd_5962485 < baseStart_5962485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962524 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_5962524 : Nat := 118140960795 + 5962524 * 2 ^ 59
def prefixEnd_5962524 : Nat := 4983230072969 + 3 ^ 40 * 5962524 * 2
def baseEnd_5962524 : Nat := 1020546908656244943709619

theorem tailTrace_5962524 : CollatzResearch.WordTrace tailWord_5962524 prefixEnd_5962524 1020546908656244943709619 := by
  unfold tailWord_5962524
  simp only [CollatzResearch.WordTrace]
  refine ⟨108735558125400670435935313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144980744167200893914580417 108735558125400670435935313)
  ·
    refine ⟨81551668594050502826951485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108735558125400670435935313 81551668594050502826951485)
    ·
      refine ⟨30581875722768938560106807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81551668594050502826951485 30581875722768938560106807)
      ·
        refine ⟨45872813584153407840160211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30581875722768938560106807 45872813584153407840160211)
        ·
          refine ⟨68809220376230111760240317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45872813584153407840160211 68809220376230111760240317)
          ·
            refine ⟨25803457641086291910090119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68809220376230111760240317 25803457641086291910090119)
            ·
              refine ⟨38705186461629437865135179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25803457641086291910090119 38705186461629437865135179)
              ·
                refine ⟨58057779692444156797702769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38705186461629437865135179 58057779692444156797702769)
                ·
                  refine ⟨43543334769333117598277077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58057779692444156797702769 43543334769333117598277077)
                  ·
                    refine ⟨1020546908656244943709619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43543334769333117598277077 1020546908656244943709619)
                    ·
                      rfl

theorem cell23_5962524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_5962524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962524 prefixEnd_5962524 := by exact prefixLift 5962524
  have htrace : WordTrace (prefixWord ++ tailWord_5962524) baseStart_5962524 baseEnd_5962524 := by
    simpa [prefixWord, tailWord_5962524, baseEnd_5962524] using wordTrace_append hprefix tailTrace_5962524
  have hstable : (prefixWord ++ tailWord_5962524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962524).length < 2 ^ (prefixWord ++ tailWord_5962524).sum := by decide
  have hdescent : baseEnd_5962524 < baseStart_5962524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962595 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 1, 4, 2]
def baseStart_5962595 : Nat := 118140960795 + 5962595 * 2 ^ 59
def prefixEnd_5962595 : Nat := 4983230072969 + 3 ^ 40 * 5962595 * 2
def baseEnd_5962595 : Nat := 3061677183095204053341031

theorem tailTrace_5962595 : CollatzResearch.WordTrace tailWord_5962595 prefixEnd_5962595 3061677183095204053341031 := by
  unfold tailWord_5962595
  simp only [CollatzResearch.WordTrace]
  refine ⟨217473705833544119997705239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144982470555696079998470159 217473705833544119997705239)
  ·
    refine ⟨326210558750316179996557859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217473705833544119997705239 326210558750316179996557859)
    ·
      refine ⟨489315838125474269994836789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326210558750316179996557859 489315838125474269994836789)
      ·
        refine ⟨45873359824263212812015949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 489315838125474269994836789 45873359824263212812015949)
        ·
          refine ⟨17202509934098704804505981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45873359824263212812015949 17202509934098704804505981)
          ·
            refine ⟨6450941225287014301689743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17202509934098704804505981 6450941225287014301689743)
            ·
              refine ⟨9676411837930521452534615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6450941225287014301689743 9676411837930521452534615)
              ·
                refine ⟨14514617756895782178801923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676411837930521452534615 14514617756895782178801923)
                ·
                  refine ⟨21771926635343673268202885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14514617756895782178801923 21771926635343673268202885)
                  ·
                    refine ⟨4082236244126938737788041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21771926635343673268202885 4082236244126938737788041)
                    ·
                      refine ⟨3061677183095204053341031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082236244126938737788041 3061677183095204053341031)
                      ·
                        rfl

theorem cell23_5962595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_5962595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962595 prefixEnd_5962595 := by exact prefixLift 5962595
  have htrace : WordTrace (prefixWord ++ tailWord_5962595) baseStart_5962595 baseEnd_5962595 := by
    simpa [prefixWord, tailWord_5962595, baseEnd_5962595] using wordTrace_append hprefix tailTrace_5962595
  have hstable : (prefixWord ++ tailWord_5962595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962595).length < 2 ^ (prefixWord ++ tailWord_5962595).sum := by decide
  have hdescent : baseEnd_5962595 < baseStart_5962595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962631 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 4, 5]
def baseStart_5962631 : Nat := 118140960795 + 5962631 * 2 ^ 59
def prefixEnd_5962631 : Nat := 4983230072969 + 3 ^ 40 * 5962631 * 2
def baseEnd_5962631 : Nat := 1020565222799588637496955

theorem tailTrace_5962631 : CollatzResearch.WordTrace tailWord_5962631 prefixEnd_5962631 1020565222799588637496955 := by
  unfold tailWord_5962631
  simp only [CollatzResearch.WordTrace]
  refine ⟨217475018861413698146015747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144983345907609132097343831 217475018861413698146015747)
  ·
    refine ⟨326212528292120547219023621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217475018861413698146015747 326212528292120547219023621)
    ·
      refine ⟨61164849054772602603566929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326212528292120547219023621 61164849054772602603566929)
      ·
        refine ⟨45873636791079451952675197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61164849054772602603566929 45873636791079451952675197)
        ·
          refine ⟨17202613796654794482253199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45873636791079451952675197 17202613796654794482253199)
          ·
            refine ⟨25803920694982191723379799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17202613796654794482253199 25803920694982191723379799)
            ·
              refine ⟨38705881042473287585069699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25803920694982191723379799 38705881042473287585069699)
              ·
                refine ⟨58058821563709931377604549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38705881042473287585069699 58058821563709931377604549)
                ·
                  refine ⟨10886029043195612133300853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58058821563709931377604549 10886029043195612133300853)
                  ·
                    refine ⟨1020565222799588637496955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10886029043195612133300853 1020565222799588637496955)
                    ·
                      rfl

theorem cell23_5962631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_5962631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962631 prefixEnd_5962631 := by exact prefixLift 5962631
  have htrace : WordTrace (prefixWord ++ tailWord_5962631) baseStart_5962631 baseEnd_5962631 := by
    simpa [prefixWord, tailWord_5962631, baseEnd_5962631] using wordTrace_append hprefix tailTrace_5962631
  have hstable : (prefixWord ++ tailWord_5962631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962631).length < 2 ^ (prefixWord ++ tailWord_5962631).sum := by decide
  have hdescent : baseEnd_5962631 < baseStart_5962631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962646 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5962646 : Nat := 118140960795 + 5962646 * 2 ^ 59
def prefixEnd_5962646 : Nat := 4983230072969 + 3 ^ 40 * 5962646 * 2
def baseEnd_5962646 : Nat := 3061703370608583353803297

theorem tailTrace_5962646 : CollatzResearch.WordTrace tailWord_5962646 prefixEnd_5962646 3061703370608583353803297 := by
  unfold tailWord_5962646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13592222872272459731738237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144983710637572903805207861 13592222872272459731738237)
  ·
    refine ⟨5097083577102172399401839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13592222872272459731738237 5097083577102172399401839)
    ·
      refine ⟨7645625365653258599102759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5097083577102172399401839 7645625365653258599102759)
      ·
        refine ⟨11468438048479887898654139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7645625365653258599102759 11468438048479887898654139)
        ·
          refine ⟨17202657072719831847981209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11468438048479887898654139 17202657072719831847981209)
          ·
            refine ⟨12901992804539873885985907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17202657072719831847981209 12901992804539873885985907)
            ·
              refine ⟨19352989206809810828978861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12901992804539873885985907 19352989206809810828978861)
              ·
                refine ⟨7257370952553679060867073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19352989206809810828978861 7257370952553679060867073)
                ·
                  refine ⟨5443028214415259295650305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7257370952553679060867073 5443028214415259295650305)
                  ·
                    refine ⟨4082271160811444471737729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443028214415259295650305 4082271160811444471737729)
                    ·
                      refine ⟨3061703370608583353803297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082271160811444471737729 3061703370608583353803297)
                      ·
                        rfl

theorem cell23_5962646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5962646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962646 prefixEnd_5962646 := by exact prefixLift 5962646
  have htrace : WordTrace (prefixWord ++ tailWord_5962646) baseStart_5962646 baseEnd_5962646 := by
    simpa [prefixWord, tailWord_5962646, baseEnd_5962646] using wordTrace_append hprefix tailTrace_5962646
  have hstable : (prefixWord ++ tailWord_5962646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962646).length < 2 ^ (prefixWord ++ tailWord_5962646).sum := by decide
  have hdescent : baseEnd_5962646 < baseStart_5962646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962688 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3]
def baseStart_5962688 : Nat := 118140960795 + 5962688 * 2 ^ 59
def prefixEnd_5962688 : Nat := 4983230072969 + 3 ^ 40 * 5962688 * 2
def baseEnd_5962688 : Nat := 3061724936796072189478103

theorem tailTrace_5962688 : CollatzResearch.WordTrace tailWord_5962688 prefixEnd_5962688 3061724936796072189478103 := by
  unfold tailWord_5962688
  simp only [CollatzResearch.WordTrace]
  refine ⟨108738548911103598440420359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144984731881471464587227145 108738548911103598440420359)
  ·
    refine ⟨163107823366655397660630539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108738548911103598440420359 163107823366655397660630539)
    ·
      refine ⟨244661735049983096490945809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163107823366655397660630539 244661735049983096490945809)
      ·
        refine ⟨183496301287487322368209357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244661735049983096490945809 183496301287487322368209357)
        ·
          refine ⟨68811112982807745888078509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183496301287487322368209357 68811112982807745888078509)
          ·
            refine ⟨25804167368552904708029441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68811112982807745888078509 25804167368552904708029441)
            ·
              refine ⟨19353125526414678531022081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25804167368552904708029441 19353125526414678531022081)
              ·
                refine ⟨14514844144811008898266561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19353125526414678531022081 14514844144811008898266561)
                ·
                  refine ⟨10886133108608256673699921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14514844144811008898266561 10886133108608256673699921)
                  ·
                    refine ⟨8164599831456192505274941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10886133108608256673699921 8164599831456192505274941)
                    ·
                      refine ⟨3061724936796072189478103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8164599831456192505274941 3061724936796072189478103)
                      ·
                        rfl

theorem cell23_5962688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_5962688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962688 prefixEnd_5962688 := by exact prefixLift 5962688
  have htrace : WordTrace (prefixWord ++ tailWord_5962688) baseStart_5962688 baseEnd_5962688 := by
    simpa [prefixWord, tailWord_5962688, baseEnd_5962688] using wordTrace_append hprefix tailTrace_5962688
  have hstable : (prefixWord ++ tailWord_5962688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962688).length < 2 ^ (prefixWord ++ tailWord_5962688).sum := by decide
  have hdescent : baseEnd_5962688 < baseStart_5962688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962708 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 6]
def baseStart_5962708 : Nat := 118140960795 + 5962708 * 2 ^ 59
def prefixEnd_5962708 : Nat := 4983230072969 + 3 ^ 40 * 5962708 * 2
def baseEnd_5962708 : Nat := 340192800712129123469779

theorem tailTrace_5962708 : CollatzResearch.WordTrace tailWord_5962708 prefixEnd_5962708 340192800712129123469779 := by
  unfold tailWord_5962708
  simp only [CollatzResearch.WordTrace]
  refine ⟨108738913641067370148284389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144985218188089826864379185 108738913641067370148284389)
  ·
    refine ⟨20388546307700131902803323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108738913641067370148284389 20388546307700131902803323)
    ·
      refine ⟨30582819461550197854204985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20388546307700131902803323 30582819461550197854204985)
      ·
        refine ⟨22937114596162648390653739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30582819461550197854204985 22937114596162648390653739)
        ·
          refine ⟨34405671894243972585980609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22937114596162648390653739 34405671894243972585980609)
          ·
            refine ⟨25804253920682979439485457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34405671894243972585980609 25804253920682979439485457)
            ·
              refine ⟨19353190440512234579614093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25804253920682979439485457 19353190440512234579614093)
              ·
                refine ⟨7257446415192087967355285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19353190440512234579614093 7257446415192087967355285)
                ·
                  refine ⟨340192800712129123469779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7257446415192087967355285 340192800712129123469779)
                  ·
                    rfl

theorem cell23_5962708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_5962708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962708 prefixEnd_5962708 := by exact prefixLift 5962708
  have htrace : WordTrace (prefixWord ++ tailWord_5962708) baseStart_5962708 baseEnd_5962708 := by
    simpa [prefixWord, tailWord_5962708, baseEnd_5962708] using wordTrace_append hprefix tailTrace_5962708
  have hstable : (prefixWord ++ tailWord_5962708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962708).length < 2 ^ (prefixWord ++ tailWord_5962708).sum := by decide
  have hdescent : baseEnd_5962708 < baseStart_5962708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962722 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_5962722 : Nat := 118140960795 + 5962722 * 2 ^ 59
def prefixEnd_5962722 : Nat := 4983230072969 + 3 ^ 40 * 5962722 * 2
def baseEnd_5962722 : Nat := 3061742395138325056452947

theorem tailTrace_5962722 : CollatzResearch.WordTrace tailWord_5962722 prefixEnd_5962722 3061742395138325056452947 := by
  unfold tailWord_5962722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54369584476021005171894605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144985558602722680458385613 54369584476021005171894605)
  ·
    refine ⟨20388594178507876939460477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54369584476021005171894605 20388594178507876939460477)
    ·
      refine ⟨7645722816940453852297679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20388594178507876939460477 7645722816940453852297679)
      ·
        refine ⟨11468584225410680778446519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7645722816940453852297679 11468584225410680778446519)
        ·
          refine ⟨17202876338116021167669779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11468584225410680778446519 17202876338116021167669779)
          ·
            refine ⟨25804314507174031751504669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17202876338116021167669779 25804314507174031751504669)
            ·
              refine ⟨9676617940190261906814251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25804314507174031751504669 9676617940190261906814251)
              ·
                refine ⟨14514926910285392860221377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676617940190261906814251 14514926910285392860221377)
                ·
                  refine ⟨10886195182714044645166033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14514926910285392860221377 10886195182714044645166033)
                  ·
                    refine ⟨8164646387035533483874525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10886195182714044645166033 8164646387035533483874525)
                    ·
                      refine ⟨3061742395138325056452947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8164646387035533483874525 3061742395138325056452947)
                      ·
                        rfl

theorem cell23_5962722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_5962722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962722 prefixEnd_5962722 := by exact prefixLift 5962722
  have htrace : WordTrace (prefixWord ++ tailWord_5962722) baseStart_5962722 baseEnd_5962722 := by
    simpa [prefixWord, tailWord_5962722, baseEnd_5962722] using wordTrace_append hprefix tailTrace_5962722
  have hstable : (prefixWord ++ tailWord_5962722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962722).length < 2 ^ (prefixWord ++ tailWord_5962722).sum := by decide
  have hdescent : baseEnd_5962722 < baseStart_5962722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962775 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5962775 : Nat := 118140960795 + 5962775 * 2 ^ 59
def prefixEnd_5962775 : Nat := 4983230072969 + 3 ^ 40 * 5962775 * 2
def baseEnd_5962775 : Nat := 3061769609613013349090203

theorem tailTrace_5962775 : CollatzResearch.WordTrace tailWord_5962775 prefixEnd_5962775 3061769609613013349090203 := by
  unfold tailWord_5962775
  simp only [CollatzResearch.WordTrace]
  refine ⟨217480270972892010739257779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144986847315261340492838519 217480270972892010739257779)
  ·
    refine ⟨326220406459338016108886669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217480270972892010739257779 326220406459338016108886669)
    ·
      refine ⟨122332652422251756040832501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326220406459338016108886669 122332652422251756040832501)
      ·
        refine ⟨11468686164586102128828047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122332652422251756040832501 11468686164586102128828047)
        ·
          refine ⟨17203029246879153193242071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11468686164586102128828047 17203029246879153193242071)
          ·
            refine ⟨25804543870318729789863107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17203029246879153193242071 25804543870318729789863107)
            ·
              refine ⟨38706815805478094684794661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25804543870318729789863107 38706815805478094684794661)
              ·
                refine ⟨7257527963527142753398999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38706815805478094684794661 7257527963527142753398999)
                ·
                  refine ⟨10886291945290714130098499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7257527963527142753398999 10886291945290714130098499)
                  ·
                    refine ⟨16329437917936071195147749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10886291945290714130098499 16329437917936071195147749)
                    ·
                      refine ⟨3061769609613013349090203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16329437917936071195147749 3061769609613013349090203)
                      ·
                        rfl

theorem cell23_5962775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5962775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962775 prefixEnd_5962775 := by exact prefixLift 5962775
  have htrace : WordTrace (prefixWord ++ tailWord_5962775) baseStart_5962775 baseEnd_5962775 := by
    simpa [prefixWord, tailWord_5962775, baseEnd_5962775] using wordTrace_append hprefix tailTrace_5962775
  have hstable : (prefixWord ++ tailWord_5962775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962775).length < 2 ^ (prefixWord ++ tailWord_5962775).sum := by decide
  have hdescent : baseEnd_5962775 < baseStart_5962775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962809 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 3, 2, 2]
def baseStart_5962809 : Nat := 118140960795 + 5962809 * 2 ^ 59
def prefixEnd_5962809 : Nat := 4983230072969 + 3 ^ 40 * 5962809 * 2
def baseEnd_5962809 : Nat := 3061787067955266216065047

theorem tailTrace_5962809 : CollatzResearch.WordTrace tailWord_5962809 prefixEnd_5962809 3061787067955266216065047 := by
  unfold tailWord_5962809
  simp only [CollatzResearch.WordTrace]
  refine ⟨217481511054768834545995481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144987674036512556363996987 217481511054768834545995481)
  ·
    refine ⟨163111133291076625909496611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217481511054768834545995481 163111133291076625909496611)
    ·
      refine ⟨244666699936614938864244917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163111133291076625909496611 244666699936614938864244917)
      ·
        refine ⟨22937503119057650518522961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 244666699936614938864244917 22937503119057650518522961)
        ·
          refine ⟨17203127339293237888892221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22937503119057650518522961 17203127339293237888892221)
          ·
            refine ⟨6451172752234964208334583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17203127339293237888892221 6451172752234964208334583)
            ·
              refine ⟨9676759128352446312501875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451172752234964208334583 9676759128352446312501875)
              ·
                refine ⟨14515138692528669468752813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676759128352446312501875 14515138692528669468752813)
                ·
                  refine ⟨5443177009698251050782305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14515138692528669468752813 5443177009698251050782305)
                  ·
                    refine ⟨4082382757273688288086729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443177009698251050782305 4082382757273688288086729)
                    ·
                      refine ⟨3061787067955266216065047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082382757273688288086729 3061787067955266216065047)
                      ·
                        rfl

theorem cell23_5962809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_5962809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962809 prefixEnd_5962809 := by exact prefixLift 5962809
  have htrace : WordTrace (prefixWord ++ tailWord_5962809) baseStart_5962809 baseEnd_5962809 := by
    simpa [prefixWord, tailWord_5962809, baseEnd_5962809] using wordTrace_append hprefix tailTrace_5962809
  have hstable : (prefixWord ++ tailWord_5962809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962809).length < 2 ^ (prefixWord ++ tailWord_5962809).sum := by decide
  have hdescent : baseEnd_5962809 < baseStart_5962809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962829 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_5962829 : Nat := 118140960795 + 5962829 * 2 ^ 59
def prefixEnd_5962829 : Nat := 4983230072969 + 3 ^ 40 * 5962829 * 2
def baseEnd_5962829 : Nat := 3061797337568356137814955

theorem tailTrace_5962829 : CollatzResearch.WordTrace tailWord_5962829 prefixEnd_5962829 3061797337568356137814955 := by
  unfold tailWord_5962829
  simp only [CollatzResearch.WordTrace]
  refine ⟨217482240514696377961723541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144988160343130918641149027 217482240514696377961723541)
  ·
    refine ⟨10194480024126392716955791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217482240514696377961723541 10194480024126392716955791)
    ·
      refine ⟨15291720036189589075433687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10194480024126392716955791 15291720036189589075433687)
      ·
        refine ⟨22937580054284383613150531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15291720036189589075433687 22937580054284383613150531)
        ·
          refine ⟨34406370081426575419725797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22937580054284383613150531 34406370081426575419725797)
          ·
            refine ⟨6451194390267482891198587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34406370081426575419725797 6451194390267482891198587)
            ·
              refine ⟨9676791585401224336797881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451194390267482891198587 9676791585401224336797881)
              ·
                refine ⟨7257593689050918252598411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9676791585401224336797881 7257593689050918252598411)
                ·
                  refine ⟨10886390533576377378897617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7257593689050918252598411 10886390533576377378897617)
                  ·
                    refine ⟨8164792900182283034173213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10886390533576377378897617 8164792900182283034173213)
                    ·
                      refine ⟨3061797337568356137814955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8164792900182283034173213 3061797337568356137814955)
                      ·
                        rfl

theorem cell23_5962829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_5962829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962829 prefixEnd_5962829 := by exact prefixLift 5962829
  have htrace : WordTrace (prefixWord ++ tailWord_5962829) baseStart_5962829 baseEnd_5962829 := by
    simpa [prefixWord, tailWord_5962829, baseEnd_5962829] using wordTrace_append hprefix tailTrace_5962829
  have hstable : (prefixWord ++ tailWord_5962829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962829).length < 2 ^ (prefixWord ++ tailWord_5962829).sum := by decide
  have hdescent : baseEnd_5962829 < baseStart_5962829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962841 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 3, 8]
def baseStart_5962841 : Nat := 118140960795 + 5962841 * 2 ^ 59
def prefixEnd_5962841 : Nat := 4983230072969 + 3 ^ 40 * 5962841 * 2
def baseEnd_5962841 : Nat := 1020601166445403363621633

theorem tailTrace_5962841 : CollatzResearch.WordTrace tailWord_5962841 prefixEnd_5962841 1020601166445403363621633 := by
  unfold tailWord_5962841
  simp only [CollatzResearch.WordTrace]
  refine ⟨217482678190652904011160377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144988452127101936007440251 217482678190652904011160377)
  ·
    refine ⟨163112008642989678008370283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217482678190652904011160377 163112008642989678008370283)
    ·
      refine ⟨244668012964484517012555425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163112008642989678008370283 244668012964484517012555425)
      ·
        refine ⟨183501009723363387759416569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244668012964484517012555425 183501009723363387759416569)
        ·
          refine ⟨137625757292522540819562427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183501009723363387759416569 137625757292522540819562427)
          ·
            refine ⟨206438635938783811229343641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137625757292522540819562427 206438635938783811229343641)
            ·
              refine ⟨154828976954087858422007731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206438635938783811229343641 154828976954087858422007731)
              ·
                refine ⟨232243465431131787633011597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154828976954087858422007731 232243465431131787633011597)
                ·
                  refine ⟨87091299536674420362379349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232243465431131787633011597 87091299536674420362379349)
                  ·
                    refine ⟨1020601166445403363621633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87091299536674420362379349 1020601166445403363621633)
                    ·
                      rfl

theorem cell23_5962841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_5962841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962841 prefixEnd_5962841 := by exact prefixLift 5962841
  have htrace : WordTrace (prefixWord ++ tailWord_5962841) baseStart_5962841 baseEnd_5962841 := by
    simpa [prefixWord, tailWord_5962841, baseEnd_5962841] using wordTrace_append hprefix tailTrace_5962841
  have hstable : (prefixWord ++ tailWord_5962841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962841).length < 2 ^ (prefixWord ++ tailWord_5962841).sum := by decide
  have hdescent : baseEnd_5962841 < baseStart_5962841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962916 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_5962916 : Nat := 118140960795 + 5962916 * 2 ^ 59
def prefixEnd_5962916 : Nat := 4983230072969 + 3 ^ 40 * 5962916 * 2
def baseEnd_5962916 : Nat := 3061842010385297297427055

theorem tailTrace_5962916 : CollatzResearch.WordTrace tailWord_5962916 prefixEnd_5962916 3061842010385297297427055 := by
  unfold tailWord_5962916
  simp only [CollatzResearch.WordTrace]
  refine ⟨108742706832690595910070301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144990275776920794546760401 108742706832690595910070301)
  ·
    refine ⟨40778515062258973466276363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108742706832690595910070301 40778515062258973466276363)
    ·
      refine ⟨61167772593388460199414545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40778515062258973466276363 61167772593388460199414545)
      ·
        refine ⟨45875829445041345149560909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61167772593388460199414545 45875829445041345149560909)
        ·
          refine ⟨17203436041890504431085341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45875829445041345149560909 17203436041890504431085341)
          ·
            refine ⟨6451288515708939161657003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17203436041890504431085341 6451288515708939161657003)
            ·
              refine ⟨9676932773563408742485505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451288515708939161657003 9676932773563408742485505)
              ·
                refine ⟨7257699580172556556864129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9676932773563408742485505 7257699580172556556864129)
                ·
                  refine ⟨5443274685129417417648097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7257699580172556556864129 5443274685129417417648097)
                  ·
                    refine ⟨4082456013847063063236073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443274685129417417648097 4082456013847063063236073)
                    ·
                      refine ⟨3061842010385297297427055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082456013847063063236073 3061842010385297297427055)
                      ·
                        rfl

theorem cell23_5962916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_5962916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962916 prefixEnd_5962916 := by exact prefixLift 5962916
  have htrace : WordTrace (prefixWord ++ tailWord_5962916) baseStart_5962916 baseEnd_5962916 := by
    simpa [prefixWord, tailWord_5962916, baseEnd_5962916] using wordTrace_append hprefix tailTrace_5962916
  have hstable : (prefixWord ++ tailWord_5962916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962916).length < 2 ^ (prefixWord ++ tailWord_5962916).sum := by decide
  have hdescent : baseEnd_5962916 < baseStart_5962916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962922 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 7]
def baseStart_5962922 : Nat := 118140960795 + 5962922 * 2 ^ 59
def prefixEnd_5962922 : Nat := 4983230072969 + 3 ^ 40 * 5962922 * 2
def baseEnd_5962922 : Nat := 340205010141024919328003

theorem tailTrace_5962922 : CollatzResearch.WordTrace tailWord_5962922 prefixEnd_5962922 340205010141024919328003 := by
  unfold tailWord_5962922
  simp only [CollatzResearch.WordTrace]
  refine ⟨54371408125839863711214755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144990421668906303229906013 54371408125839863711214755)
  ·
    refine ⟨81557112188759795566822133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54371408125839863711214755 81557112188759795566822133)
    ·
      refine ⟨7645979267696230834389575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81557112188759795566822133 7645979267696230834389575)
      ·
        refine ⟨11468968901544346251584363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7645979267696230834389575 11468968901544346251584363)
        ·
          refine ⟨17203453352316519377376545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11468968901544346251584363 17203453352316519377376545)
          ·
            refine ⟨12902590014237389533032409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17203453352316519377376545 12902590014237389533032409)
            ·
              refine ⟨9676942510678042149774307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12902590014237389533032409 9676942510678042149774307)
              ·
                refine ⟨14515413766017063224661461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9676942510678042149774307 14515413766017063224661461)
                ·
                  refine ⟨340205010141024919328003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14515413766017063224661461 340205010141024919328003)
                  ·
                    rfl

theorem cell23_5962922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_5962922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962922 prefixEnd_5962922 := by exact prefixLift 5962922
  have htrace : WordTrace (prefixWord ++ tailWord_5962922) baseStart_5962922 baseEnd_5962922 := by
    simpa [prefixWord, tailWord_5962922, baseEnd_5962922] using wordTrace_append hprefix tailTrace_5962922
  have hstable : (prefixWord ++ tailWord_5962922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962922).length < 2 ^ (prefixWord ++ tailWord_5962922).sum := by decide
  have hdescent : baseEnd_5962922 < baseStart_5962922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962955 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 4, 4, 2]
def baseStart_5962955 : Nat := 118140960795 + 5962955 * 2 ^ 59
def prefixEnd_5962955 : Nat := 4983230072969 + 3 ^ 40 * 5962955 * 2
def baseEnd_5962955 : Nat := 3061862036130822644839375

theorem tailTrace_5962955 : CollatzResearch.WordTrace tailWord_5962955 prefixEnd_5962955 3061862036130822644839375 := by
  unfold tailWord_5962955
  simp only [CollatzResearch.WordTrace]
  refine ⟨217486836112239901480810319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144991224074826600987206879 217486836112239901480810319)
  ·
    refine ⟨326230254168359852221215479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217486836112239901480810319 326230254168359852221215479)
    ·
      refine ⟨489345381252539778331823219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326230254168359852221215479 489345381252539778331823219)
      ·
        refine ⟨734018071878809667497734829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489345381252539778331823219 734018071878809667497734829)
        ·
          refine ⟨275256776954553625311650561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 734018071878809667497734829 275256776954553625311650561)
          ·
            refine ⟨206442582715915218983737921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275256776954553625311650561 206442582715915218983737921)
            ·
              refine ⟨154831937036936414237803441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206442582715915218983737921 154831937036936414237803441)
              ·
                refine ⟨116123952777702310678352581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154831937036936414237803441 116123952777702310678352581)
                ·
                  refine ⟨21773241145819183252191109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116123952777702310678352581 21773241145819183252191109)
                  ·
                    refine ⟨4082482714841096859785833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21773241145819183252191109 4082482714841096859785833)
                    ·
                      refine ⟨3061862036130822644839375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082482714841096859785833 3061862036130822644839375)
                      ·
                        rfl

theorem cell23_5962955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 4, 2].length) (baseStart_5962955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962955 prefixEnd_5962955 := by exact prefixLift 5962955
  have htrace : WordTrace (prefixWord ++ tailWord_5962955) baseStart_5962955 baseEnd_5962955 := by
    simpa [prefixWord, tailWord_5962955, baseEnd_5962955] using wordTrace_append hprefix tailTrace_5962955
  have hstable : (prefixWord ++ tailWord_5962955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962955).length < 2 ^ (prefixWord ++ tailWord_5962955).sum := by decide
  have hdescent : baseEnd_5962955 < baseStart_5962955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962975 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 3]
def baseStart_5962975 : Nat := 118140960795 + 5962975 * 2 ^ 59
def prefixEnd_5962975 : Nat := 4983230072969 + 3 ^ 40 * 5962975 * 2
def baseEnd_5962975 : Nat := 3061872305743912566589283

theorem tailTrace_5962975 : CollatzResearch.WordTrace tailWord_5962975 prefixEnd_5962975 3061872305743912566589283 := by
  unfold tailWord_5962975
  simp only [CollatzResearch.WordTrace]
  refine ⟨217487565572167444896538379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144991710381444963264358919 217487565572167444896538379)
  ·
    refine ⟨326231348358251167344807569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217487565572167444896538379 326231348358251167344807569)
    ·
      refine ⟨244673511268688375508605677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326231348358251167344807569 244673511268688375508605677)
      ·
        refine ⟨91752566725758140815727129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244673511268688375508605677 91752566725758140815727129)
        ·
          refine ⟨68814425044318605611795347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91752566725758140815727129 68814425044318605611795347)
          ·
            refine ⟨103221637566477908417693021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68814425044318605611795347 103221637566477908417693021)
            ·
              refine ⟨38708114087429215656634883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103221637566477908417693021 38708114087429215656634883)
              ·
                refine ⟨58062171131143823484952325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38708114087429215656634883 58062171131143823484952325)
                ·
                  refine ⟨10886657087089466903428561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58062171131143823484952325 10886657087089466903428561)
                  ·
                    refine ⟨8164992815317100177571421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10886657087089466903428561 8164992815317100177571421)
                    ·
                      refine ⟨3061872305743912566589283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8164992815317100177571421 3061872305743912566589283)
                      ·
                        rfl

theorem cell23_5962975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_5962975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962975 prefixEnd_5962975 := by exact prefixLift 5962975
  have htrace : WordTrace (prefixWord ++ tailWord_5962975) baseStart_5962975 baseEnd_5962975 := by
    simpa [prefixWord, tailWord_5962975, baseEnd_5962975] using wordTrace_append hprefix tailTrace_5962975
  have hstable : (prefixWord ++ tailWord_5962975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962975).length < 2 ^ (prefixWord ++ tailWord_5962975).sum := by decide
  have hdescent : baseEnd_5962975 < baseStart_5962975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5962995 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 6]
def baseStart_5962995 : Nat := 118140960795 + 5962995 * 2 ^ 59
def prefixEnd_5962995 : Nat := 4983230072969 + 3 ^ 40 * 5962995 * 2
def baseEnd_5962995 : Nat := 340209175039666943148799

theorem tailTrace_5962995 : CollatzResearch.WordTrace tailWord_5962995 prefixEnd_5962995 340209175039666943148799 := by
  unfold tailWord_5962995
  simp only [CollatzResearch.WordTrace]
  refine ⟨217488295032094988312266439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144992196688063325541510959 217488295032094988312266439)
  ·
    refine ⟨326232442548142482468399659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217488295032094988312266439 326232442548142482468399659)
    ·
      refine ⟨489348663822213723702599489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326232442548142482468399659 489348663822213723702599489)
      ·
        refine ⟨367011497866660292776949617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489348663822213723702599489 367011497866660292776949617)
        ·
          refine ⟨275258623399995219582712213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367011497866660292776949617 275258623399995219582712213)
          ·
            refine ⟨12902747971874775917939635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 275258623399995219582712213 12902747971874775917939635)
            ·
              refine ⟨19354121957812163876909453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12902747971874775917939635 19354121957812163876909453)
              ·
                refine ⟨7257795734179561453841045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19354121957812163876909453 7257795734179561453841045)
                ·
                  refine ⟨340209175039666943148799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7257795734179561453841045 340209175039666943148799)
                  ·
                    rfl

theorem cell23_5962995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 6].length) (baseStart_5962995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5962995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5962995 prefixEnd_5962995 := by exact prefixLift 5962995
  have htrace : WordTrace (prefixWord ++ tailWord_5962995) baseStart_5962995 baseEnd_5962995 := by
    simpa [prefixWord, tailWord_5962995, baseEnd_5962995] using wordTrace_append hprefix tailTrace_5962995
  have hstable : (prefixWord ++ tailWord_5962995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5962995).length < 2 ^ (prefixWord ++ tailWord_5962995).sum := by decide
  have hdescent : baseEnd_5962995 < baseStart_5962995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5962995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963055 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 6, 4]
def baseStart_5963055 : Nat := 118140960795 + 5963055 * 2 ^ 59
def prefixEnd_5963055 : Nat := 4983230072969 + 3 ^ 40 * 5963055 * 2
def baseEnd_5963055 : Nat := 1020637794732090751196305

theorem tailTrace_5963055 : CollatzResearch.WordTrace tailWord_5963055 prefixEnd_5963055 1020637794732090751196305 := by
  unfold tailWord_5963055
  simp only [CollatzResearch.WordTrace]
  refine ⟨217490483411877618559450619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144993655607918412372967079 217490483411877618559450619)
  ·
    refine ⟨326235725117816427839175929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217490483411877618559450619 326235725117816427839175929)
    ·
      refine ⟨244676793838362320879381947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326235725117816427839175929 244676793838362320879381947)
      ·
        refine ⟨367015190757543481319072921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244676793838362320879381947 367015190757543481319072921)
        ·
          refine ⟨275261393068157610989304691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367015190757543481319072921 275261393068157610989304691)
          ·
            refine ⟨412892089602236416483957037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275261393068157610989304691 412892089602236416483957037)
            ·
              refine ⟨154834533600838656181483889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412892089602236416483957037 154834533600838656181483889)
              ·
                refine ⟨116125900200628992136112917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154834533600838656181483889 116125900200628992136112917)
                ·
                  refine ⟨5443401571904484006380293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116125900200628992136112917 5443401571904484006380293)
                  ·
                    refine ⟨1020637794732090751196305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5443401571904484006380293 1020637794732090751196305)
                    ·
                      rfl

theorem cell23_5963055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_5963055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963055 prefixEnd_5963055 := by exact prefixLift 5963055
  have htrace : WordTrace (prefixWord ++ tailWord_5963055) baseStart_5963055 baseEnd_5963055 := by
    simpa [prefixWord, tailWord_5963055, baseEnd_5963055] using wordTrace_append hprefix tailTrace_5963055
  have hstable : (prefixWord ++ tailWord_5963055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963055).length < 2 ^ (prefixWord ++ tailWord_5963055).sum := by decide
  have hdescent : baseEnd_5963055 < baseStart_5963055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963073 : List Nat := [1, 2, 5, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5963073 : Nat := 118140960795 + 5963073 * 2 ^ 59
def prefixEnd_5963073 : Nat := 4983230072969 + 3 ^ 40 * 5963073 * 2
def baseEnd_5963073 : Nat := 3061922626848053183163833

theorem tailTrace_5963073 : CollatzResearch.WordTrace tailWord_5963073 prefixEnd_5963073 3061922626848053183163833 := by
  unfold tailWord_5963073
  simp only [CollatzResearch.WordTrace]
  refine ⟨217491139925812407633605873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144994093283874938422403915 217491139925812407633605873)
  ·
    refine ⟨163118354944359305725204405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217491139925812407633605873 163118354944359305725204405)
    ·
      refine ⟨15292345776033684911737913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163118354944359305725204405 15292345776033684911737913)
      ·
        refine ⟨11469259332025263683803435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15292345776033684911737913 11469259332025263683803435)
        ·
          refine ⟨17203888998037895525705153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11469259332025263683803435 17203888998037895525705153)
          ·
            refine ⟨12902916748528421644278865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17203888998037895525705153 12902916748528421644278865)
            ·
              refine ⟨9677187561396316233209149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12902916748528421644278865 9677187561396316233209149)
              ·
                refine ⟨3628945335523618587453431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9677187561396316233209149 3628945335523618587453431)
                ·
                  refine ⟨5443418003285427881180147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628945335523618587453431 5443418003285427881180147)
                  ·
                    refine ⟨8165127004928141821770221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5443418003285427881180147 8165127004928141821770221)
                    ·
                      refine ⟨3061922626848053183163833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8165127004928141821770221 3061922626848053183163833)
                      ·
                        rfl

theorem cell23_5963073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5963073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963073 prefixEnd_5963073 := by exact prefixLift 5963073
  have htrace : WordTrace (prefixWord ++ tailWord_5963073) baseStart_5963073 baseEnd_5963073 := by
    simpa [prefixWord, tailWord_5963073, baseEnd_5963073] using wordTrace_append hprefix tailTrace_5963073
  have hstable : (prefixWord ++ tailWord_5963073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963073).length < 2 ^ (prefixWord ++ tailWord_5963073).sum := by decide
  have hdescent : baseEnd_5963073 < baseStart_5963073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963076 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_5963076 : Nat := 118140960795 + 5963076 * 2 ^ 59
def prefixEnd_5963076 : Nat := 4983230072969 + 3 ^ 40 * 5963076 * 2
def baseEnd_5963076 : Nat := 1020641389096672223808773

theorem tailTrace_5963076 : CollatzResearch.WordTrace tailWord_5963076 prefixEnd_5963076 1020641389096672223808773 := by
  unfold tailWord_5963076
  simp only [CollatzResearch.WordTrace]
  refine ⟨108745624672400769572982541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144994166229867692763976721 108745624672400769572982541)
  ·
    refine ⟨40779609252150288589868453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108745624672400769572982541 40779609252150288589868453)
    ·
      refine ⟨7646176734778179110600335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40779609252150288589868453 7646176734778179110600335)
      ·
        refine ⟨11469265102167268665900503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7646176734778179110600335 11469265102167268665900503)
        ·
          refine ⟨17203897653250902998850755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11469265102167268665900503 17203897653250902998850755)
          ·
            refine ⟨25805846479876354498276133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17203897653250902998850755 25805846479876354498276133)
            ·
              refine ⟨4838596214976816468426775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25805846479876354498276133 4838596214976816468426775)
              ·
                refine ⟨7257894322465224702640163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4838596214976816468426775 7257894322465224702640163)
                ·
                  refine ⟨10886841483697837053960245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7257894322465224702640163 10886841483697837053960245)
                  ·
                    refine ⟨1020641389096672223808773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10886841483697837053960245 1020641389096672223808773)
                    ·
                      rfl

theorem cell23_5963076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_5963076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963076 prefixEnd_5963076 := by exact prefixLift 5963076
  have htrace : WordTrace (prefixWord ++ tailWord_5963076) baseStart_5963076 baseEnd_5963076 := by
    simpa [prefixWord, tailWord_5963076, baseEnd_5963076] using wordTrace_append hprefix tailTrace_5963076
  have hstable : (prefixWord ++ tailWord_5963076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963076).length < 2 ^ (prefixWord ++ tailWord_5963076).sum := by decide
  have hdescent : baseEnd_5963076 < baseStart_5963076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963079 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_5963079 : Nat := 118140960795 + 5963079 * 2 ^ 59
def prefixEnd_5963079 : Nat := 4983230072969 + 3 ^ 40 * 5963079 * 2
def baseEnd_5963079 : Nat := 3061925707731980159688805

theorem tailTrace_5963079 : CollatzResearch.WordTrace tailWord_5963079 prefixEnd_5963079 3061925707731980159688805 := by
  unfold tailWord_5963079
  simp only [CollatzResearch.WordTrace]
  refine ⟨217491358763790670658324291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144994239175860447105549527 217491358763790670658324291)
  ·
    refine ⟨326237038145686005987486437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217491358763790670658324291 326237038145686005987486437)
    ·
      refine ⟨61169444652316126122653707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326237038145686005987486437 61169444652316126122653707)
      ·
        refine ⟨91754166978474189183980561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61169444652316126122653707 91754166978474189183980561)
        ·
          refine ⟨68815625233855641887985421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91754166978474189183980561 68815625233855641887985421)
          ·
            refine ⟨25805859462695865707994533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68815625233855641887985421 25805859462695865707994533)
            ·
              refine ⟨4838598649255474820248975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25805859462695865707994533 4838598649255474820248975)
              ·
                refine ⟨7257897973883212230373463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4838598649255474820248975 7257897973883212230373463)
                ·
                  refine ⟨10886846960824818345560195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7257897973883212230373463 10886846960824818345560195)
                  ·
                    refine ⟨16330270441237227518340293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10886846960824818345560195 16330270441237227518340293)
                    ·
                      refine ⟨3061925707731980159688805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16330270441237227518340293 3061925707731980159688805)
                      ·
                        rfl

theorem cell23_5963079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_5963079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963079 prefixEnd_5963079 := by exact prefixLift 5963079
  have htrace : WordTrace (prefixWord ++ tailWord_5963079) baseStart_5963079 baseEnd_5963079 := by
    simpa [prefixWord, tailWord_5963079, baseEnd_5963079] using wordTrace_append hprefix tailTrace_5963079
  have hstable : (prefixWord ++ tailWord_5963079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963079).length < 2 ^ (prefixWord ++ tailWord_5963079).sum := by decide
  have hdescent : baseEnd_5963079 < baseStart_5963079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963096 : List Nat := [2, 1, 2, 2, 1, 1, 3, 6, 1, 2, 2]
def baseStart_5963096 : Nat := 118140960795 + 5963096 * 2 ^ 59
def prefixEnd_5963096 : Nat := 4983230072969 + 3 ^ 40 * 5963096 * 2
def baseEnd_5963096 : Nat := 3061934436903106593176227

theorem tailTrace_5963096 : CollatzResearch.WordTrace tailWord_5963096 prefixEnd_5963096 3061934436903106593176227 := by
  unfold tailWord_5963096
  simp only [CollatzResearch.WordTrace]
  refine ⟨108745989402364541280846571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144994652536486055041128761 108745989402364541280846571)
  ·
    refine ⟨163118984103546811921269857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108745989402364541280846571 163118984103546811921269857)
    ·
      refine ⟨122339238077660108940952393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163118984103546811921269857 122339238077660108940952393)
      ·
        refine ⟨91754428558245081705714295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122339238077660108940952393 91754428558245081705714295)
        ·
          refine ⟨137631642837367622558571443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91754428558245081705714295 137631642837367622558571443)
          ·
            refine ⟨206447464256051433837857165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137631642837367622558571443 206447464256051433837857165)
            ·
              refine ⟨77417799096019287689196437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206447464256051433837857165 77417799096019287689196437)
              ·
                refine ⟨3628959332625904110431083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77417799096019287689196437 3628959332625904110431083)
                ·
                  refine ⟨5443438998938856165646625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3628959332625904110431083 5443438998938856165646625)
                  ·
                    refine ⟨4082579249204142124234969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443438998938856165646625 4082579249204142124234969)
                    ·
                      refine ⟨3061934436903106593176227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082579249204142124234969 3061934436903106593176227)
                      ·
                        rfl

theorem cell23_5963096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_5963096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963096 prefixEnd_5963096 := by exact prefixLift 5963096
  have htrace : WordTrace (prefixWord ++ tailWord_5963096) baseStart_5963096 baseEnd_5963096 := by
    simpa [prefixWord, tailWord_5963096, baseEnd_5963096] using wordTrace_append hprefix tailTrace_5963096
  have hstable : (prefixWord ++ tailWord_5963096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963096).length < 2 ^ (prefixWord ++ tailWord_5963096).sum := by decide
  have hdescent : baseEnd_5963096 < baseStart_5963096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963106 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_5963106 : Nat := 118140960795 + 5963106 * 2 ^ 59
def prefixEnd_5963106 : Nat := 4983230072969 + 3 ^ 40 * 5963106 * 2
def baseEnd_5963106 : Nat := 1020646523903217184683727

theorem tailTrace_5963106 : CollatzResearch.WordTrace tailWord_5963106 prefixEnd_5963106 1020646523903217184683727 := by
  unfold tailWord_5963106
  simp only [CollatzResearch.WordTrace]
  refine ⟨54373085883673213567389293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144994895689795236179704781 54373085883673213567389293)
  ·
    refine ⟨20389907206377455087770985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54373085883673213567389293 20389907206377455087770985)
    ·
      refine ⟨15292430404783091315828239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20389907206377455087770985 15292430404783091315828239)
      ·
        refine ⟨22938645607174636973742359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15292430404783091315828239 22938645607174636973742359)
        ·
          refine ⟨34407968410761955460613539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22938645607174636973742359 34407968410761955460613539)
          ·
            refine ⟨51611952616142933190920309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34407968410761955460613539 51611952616142933190920309)
            ·
              refine ⟨4838620557763399986648779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51611952616142933190920309 4838620557763399986648779)
              ·
                refine ⟨7257930836645099979973169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4838620557763399986648779 7257930836645099979973169)
                ·
                  refine ⟨5443448127483824984979877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7257930836645099979973169 5443448127483824984979877)
                  ·
                    refine ⟨1020646523903217184683727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5443448127483824984979877 1020646523903217184683727)
                    ·
                      rfl

theorem cell23_5963106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_5963106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963106 prefixEnd_5963106 := by exact prefixLift 5963106
  have htrace : WordTrace (prefixWord ++ tailWord_5963106) baseStart_5963106 baseEnd_5963106 := by
    simpa [prefixWord, tailWord_5963106, baseEnd_5963106] using wordTrace_append hprefix tailTrace_5963106
  have hstable : (prefixWord ++ tailWord_5963106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963106).length < 2 ^ (prefixWord ++ tailWord_5963106).sum := by decide
  have hdescent : baseEnd_5963106 < baseStart_5963106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963239 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 2, 5]
def baseStart_5963239 : Nat := 118140960795 + 5963239 * 2 ^ 59
def prefixEnd_5963239 : Nat := 4983230072969 + 3 ^ 40 * 5963239 * 2
def baseEnd_5963239 : Nat := 1020669288212233177896023

theorem tailTrace_5963239 : CollatzResearch.WordTrace tailWord_5963239 prefixEnd_5963239 1020669288212233177896023 := by
  unfold tailWord_5963239
  simp only [CollatzResearch.WordTrace]
  refine ⟨217497194443211017984148771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144998129628807345322765847 217497194443211017984148771)
  ·
    refine ⟨326245791664816526976223157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217497194443211017984148771 326245791664816526976223157)
    ·
      refine ⟨30585542968576549404020921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326245791664816526976223157 30585542968576549404020921)
      ·
        refine ⟨22939157226432412053015691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30585542968576549404020921 22939157226432412053015691)
        ·
          refine ⟨34408735839648618079523537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22939157226432412053015691 34408735839648618079523537)
          ·
            refine ⟨25806551879736463559642653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34408735839648618079523537 25806551879736463559642653)
            ·
              refine ⟨9677456954901173834865995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25806551879736463559642653 9677456954901173834865995)
              ·
                refine ⟨14516185432351760752298993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9677456954901173834865995 14516185432351760752298993)
                ·
                  refine ⟨10887139074263820564224245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14516185432351760752298993 10887139074263820564224245)
                  ·
                    refine ⟨1020669288212233177896023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10887139074263820564224245 1020669288212233177896023)
                    ·
                      rfl

theorem cell23_5963239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_5963239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963239 prefixEnd_5963239 := by exact prefixLift 5963239
  have htrace : WordTrace (prefixWord ++ tailWord_5963239) baseStart_5963239 baseEnd_5963239 := by
    simpa [prefixWord, tailWord_5963239, baseEnd_5963239] using wordTrace_append hprefix tailTrace_5963239
  have hstable : (prefixWord ++ tailWord_5963239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963239).length < 2 ^ (prefixWord ++ tailWord_5963239).sum := by decide
  have hdescent : baseEnd_5963239 < baseStart_5963239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963294 : List Nat := [4, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_5963294 : Nat := 118140960795 + 5963294 * 2 ^ 59
def prefixEnd_5963294 : Nat := 4983230072969 + 3 ^ 40 * 5963294 * 2
def baseEnd_5963294 : Nat := 340226234008077424277813

theorem tailTrace_5963294 : CollatzResearch.WordTrace tailWord_5963294 prefixEnd_5963294 340226234008077424277813 := by
  unfold tailWord_5963294
  simp only [CollatzResearch.WordTrace]
  refine ⟨27187400057251470297175117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144999466972007841584933957 27187400057251470297175117)
  ·
    refine ⟨10195275021469301361440669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27187400057251470297175117 10195275021469301361440669)
    ·
      refine ⟨3823228133050988010540251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10195275021469301361440669 3823228133050988010540251)
      ·
        refine ⟨5734842199576482015810377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823228133050988010540251 5734842199576482015810377)
        ·
          refine ⟨4301131649682361511857783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5734842199576482015810377 4301131649682361511857783)
          ·
            refine ⟨6451697474523542267786675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301131649682361511857783 6451697474523542267786675)
            ·
              refine ⟨9677546211785313401680013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6451697474523542267786675 9677546211785313401680013)
              ·
                refine ⟨3629079829419492525630005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9677546211785313401680013 3629079829419492525630005)
                ·
                  refine ⟨340226234008077424277813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3629079829419492525630005 340226234008077424277813)
                  ·
                    rfl

theorem cell23_5963294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_5963294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963294 prefixEnd_5963294 := by exact prefixLift 5963294
  have htrace : WordTrace (prefixWord ++ tailWord_5963294) baseStart_5963294 baseEnd_5963294 := by
    simpa [prefixWord, tailWord_5963294, baseEnd_5963294] using wordTrace_append hprefix tailTrace_5963294
  have hstable : (prefixWord ++ tailWord_5963294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963294).length < 2 ^ (prefixWord ++ tailWord_5963294).sum := by decide
  have hdescent : baseEnd_5963294 < baseStart_5963294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963312 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 5, 5]
def baseStart_5963312 : Nat := 118140960795 + 5963312 * 2 ^ 59
def prefixEnd_5963312 : Nat := 4983230072969 + 3 ^ 40 * 5963312 * 2
def baseEnd_5963312 : Nat := 1020681782908159249358411

theorem tailTrace_5963312 : CollatzResearch.WordTrace tailWord_5963312 prefixEnd_5963312 1020681782908159249358411 := by
  unfold tailWord_5963312
  simp only [CollatzResearch.WordTrace]
  refine ⟨108749928485973275725778095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144999904647964367634370793 108749928485973275725778095)
  ·
    refine ⟨163124892728959913588667143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108749928485973275725778095 163124892728959913588667143)
    ·
      refine ⟨244687339093439870383000715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163124892728959913588667143 244687339093439870383000715)
      ·
        refine ⟨367031008640159805574501073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244687339093439870383000715 367031008640159805574501073)
        ·
          refine ⟨275273256480119854180875805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367031008640159805574501073 275273256480119854180875805)
          ·
            refine ⟨103227471180044945317828427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275273256480119854180875805 103227471180044945317828427)
            ·
              refine ⟨154841206770067417976742641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103227471180044945317828427 154841206770067417976742641)
              ·
                refine ⟨116130905077550563482556981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154841206770067417976742641 116130905077550563482556981)
                ·
                  refine ⟨10887272351020365326489717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116130905077550563482556981 10887272351020365326489717)
                  ·
                    refine ⟨1020681782908159249358411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10887272351020365326489717 1020681782908159249358411)
                    ·
                      rfl

theorem cell23_5963312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_5963312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963312 prefixEnd_5963312 := by exact prefixLift 5963312
  have htrace : WordTrace (prefixWord ++ tailWord_5963312) baseStart_5963312 baseEnd_5963312 := by
    simpa [prefixWord, tailWord_5963312, baseEnd_5963312] using wordTrace_append hprefix tailTrace_5963312
  have hstable : (prefixWord ++ tailWord_5963312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963312).length < 2 ^ (prefixWord ++ tailWord_5963312).sum := by decide
  have hdescent : baseEnd_5963312 < baseStart_5963312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963329 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 3, 5]
def baseStart_5963329 : Nat := 118140960795 + 5963329 * 2 ^ 59
def prefixEnd_5963329 : Nat := 4983230072969 + 3 ^ 40 * 5963329 * 2
def baseEnd_5963329 : Nat := 1020684692631868060520885

theorem tailTrace_5963329 : CollatzResearch.WordTrace tailWord_5963329 prefixEnd_5963329 1020684692631868060520885 := by
  unfold tailWord_5963329
  simp only [CollatzResearch.WordTrace]
  refine ⟨217500477012884963354925041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145000318008589975569950027 217500477012884963354925041)
  ·
    refine ⟨163125357759663722516193781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217500477012884963354925041 163125357759663722516193781)
    ·
      refine ⟨15293002289968473985893167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163125357759663722516193781 15293002289968473985893167)
      ·
        refine ⟨22939503434952710978839751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15293002289968473985893167 22939503434952710978839751)
        ·
          refine ⟨34409255152429066468259627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22939503434952710978839751 34409255152429066468259627)
          ·
            refine ⟨51613882728643599702389441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34409255152429066468259627 51613882728643599702389441)
            ·
              refine ⟨38710412046482699776792081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51613882728643599702389441 38710412046482699776792081)
              ·
                refine ⟨29032809034862024832594061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38710412046482699776792081 29032809034862024832594061)
                ·
                  refine ⟨10887303388073259312222773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29032809034862024832594061 10887303388073259312222773)
                  ·
                    refine ⟨1020684692631868060520885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10887303388073259312222773 1020684692631868060520885)
                    ·
                      rfl

theorem cell23_5963329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_5963329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963329 prefixEnd_5963329 := by exact prefixLift 5963329
  have htrace : WordTrace (prefixWord ++ tailWord_5963329) baseStart_5963329 baseEnd_5963329 := by
    simpa [prefixWord, tailWord_5963329, baseEnd_5963329] using wordTrace_append hprefix tailTrace_5963329
  have hstable : (prefixWord ++ tailWord_5963329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963329).length < 2 ^ (prefixWord ++ tailWord_5963329).sum := by decide
  have hdescent : baseEnd_5963329 < baseStart_5963329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963346 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_5963346 : Nat := 118140960795 + 5963346 * 2 ^ 59
def prefixEnd_5963346 : Nat := 4983230072969 + 3 ^ 40 * 5963346 * 2
def baseEnd_5963346 : Nat := 1020687602355576871683359

theorem tailTrace_5963346 : CollatzResearch.WordTrace tailWord_5963346 prefixEnd_5963346 1020687602355576871683359 := by
  unfold tailWord_5963346
  simp only [CollatzResearch.WordTrace]
  refine ⟨54375274263455843814573473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145000731369215583505529261 54375274263455843814573473)
  ·
    refine ⟨40781455697591882860930105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54375274263455843814573473 40781455697591882860930105)
    ·
      refine ⟨30586091773193912145697579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40781455697591882860930105 30586091773193912145697579)
      ·
        refine ⟨45879137659790868218546369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30586091773193912145697579 45879137659790868218546369)
        ·
          refine ⟨34409353244843151163909777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45879137659790868218546369 34409353244843151163909777)
          ·
            refine ⟨25807014933632363372932333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34409353244843151163909777 25807014933632363372932333)
            ·
              refine ⟨9677630600112136264849625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25807014933632363372932333 9677630600112136264849625)
              ·
                refine ⟨7258222950084102198637219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9677630600112136264849625 7258222950084102198637219)
                ·
                  refine ⟨10887334425126153297955829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7258222950084102198637219 10887334425126153297955829)
                  ·
                    refine ⟨1020687602355576871683359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10887334425126153297955829 1020687602355576871683359)
                    ·
                      rfl

theorem cell23_5963346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_5963346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963346 prefixEnd_5963346 := by exact prefixLift 5963346
  have htrace : WordTrace (prefixWord ++ tailWord_5963346) baseStart_5963346 baseEnd_5963346 := by
    simpa [prefixWord, tailWord_5963346, baseEnd_5963346] using wordTrace_append hprefix tailTrace_5963346
  have hstable : (prefixWord ++ tailWord_5963346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963346).length < 2 ^ (prefixWord ++ tailWord_5963346).sum := by decide
  have hdescent : baseEnd_5963346 < baseStart_5963346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963369 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 5]
def baseStart_5963369 : Nat := 118140960795 + 5963369 * 2 ^ 59
def prefixEnd_5963369 : Nat := 4983230072969 + 3 ^ 40 * 5963369 * 2
def baseEnd_5963369 : Nat := 3062074617121784025062471

theorem tailTrace_5963369 : CollatzResearch.WordTrace tailWord_5963369 prefixEnd_5963369 3062074617121784025062471 := by
  unfold tailWord_5963369
  simp only [CollatzResearch.WordTrace]
  refine ⟨217501935932740050186381161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145001290621826700124254107 217501935932740050186381161)
  ·
    refine ⟨163126451949555037639785871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217501935932740050186381161 163126451949555037639785871)
    ·
      refine ⟨244689677924332556459678807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163126451949555037639785871 244689677924332556459678807)
      ·
        refine ⟨367034516886498834689518211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244689677924332556459678807 367034516886498834689518211)
        ·
          refine ⟨550551775329748252034277317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367034516886498834689518211 550551775329748252034277317)
          ·
            refine ⟨103228457874327797256426997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 550551775329748252034277317 103228457874327797256426997)
            ·
              refine ⟨9677667925718230992790031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103228457874327797256426997 9677667925718230992790031)
              ·
                refine ⟨14516501888577346489185047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9677667925718230992790031 14516501888577346489185047)
                ·
                  refine ⟨21774752832866019733777571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14516501888577346489185047 21774752832866019733777571)
                  ·
                    refine ⟨32662129249299029600666357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21774752832866019733777571 32662129249299029600666357)
                    ·
                      refine ⟨3062074617121784025062471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32662129249299029600666357 3062074617121784025062471)
                      ·
                        rfl

theorem cell23_5963369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_5963369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963369 prefixEnd_5963369 := by exact prefixLift 5963369
  have htrace : WordTrace (prefixWord ++ tailWord_5963369) baseStart_5963369 baseEnd_5963369 := by
    simpa [prefixWord, tailWord_5963369, baseEnd_5963369] using wordTrace_append hprefix tailTrace_5963369
  have hstable : (prefixWord ++ tailWord_5963369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963369).length < 2 ^ (prefixWord ++ tailWord_5963369).sum := by decide
  have hdescent : baseEnd_5963369 < baseStart_5963369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963376 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 2, 4]
def baseStart_5963376 : Nat := 118140960795 + 5963376 * 2 ^ 59
def prefixEnd_5963376 : Nat := 4983230072969 + 3 ^ 40 * 5963376 * 2
def baseEnd_5963376 : Nat := 1020692737162121832558313

theorem tailTrace_5963376 : CollatzResearch.WordTrace tailWord_5963376 prefixEnd_5963376 1020692737162121832558313 := by
  unfold tailWord_5963376
  simp only [CollatzResearch.WordTrace]
  refine ⟨108751095621857345190942991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145001460829143126921257321 108751095621857345190942991)
  ·
    refine ⟨163126643432786017786414487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108751095621857345190942991 163126643432786017786414487)
    ·
      refine ⟨244689965149179026679621731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163126643432786017786414487 244689965149179026679621731)
      ·
        refine ⟨367034947723768540019432597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244689965149179026679621731 367034947723768540019432597)
        ·
          refine ⟨17204763174551650313410903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 367034947723768540019432597 17204763174551650313410903)
          ·
            refine ⟨25807144761827475470116355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17204763174551650313410903 25807144761827475470116355)
            ·
              refine ⟨38710717142741213205174533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25807144761827475470116355 38710717142741213205174533)
              ·
                refine ⟨7258259464263977475970225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38710717142741213205174533 7258259464263977475970225)
                ·
                  refine ⟨5443694598197983106977669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7258259464263977475970225 5443694598197983106977669)
                  ·
                    refine ⟨1020692737162121832558313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5443694598197983106977669 1020692737162121832558313)
                    ·
                      rfl

theorem cell23_5963376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_5963376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963376 prefixEnd_5963376 := by exact prefixLift 5963376
  have htrace : WordTrace (prefixWord ++ tailWord_5963376) baseStart_5963376 baseEnd_5963376 := by
    simpa [prefixWord, tailWord_5963376, baseEnd_5963376] using wordTrace_append hprefix tailTrace_5963376
  have hstable : (prefixWord ++ tailWord_5963376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963376).length < 2 ^ (prefixWord ++ tailWord_5963376).sum := by decide
  have hdescent : baseEnd_5963376 < baseStart_5963376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963389 : List Nat := [1, 4, 1, 1, 4, 1, 3, 8]
def baseStart_5963389 : Nat := 118140960795 + 5963389 * 2 ^ 59
def prefixEnd_5963389 : Nat := 4983230072969 + 3 ^ 40 * 5963389 * 2
def baseEnd_5963389 : Nat := 113410551360550886918977

theorem tailTrace_5963389 : CollatzResearch.WordTrace tailWord_5963389 prefixEnd_5963389 113410551360550886918977 := by
  unfold tailWord_5963389
  simp only [CollatzResearch.WordTrace]
  refine ⟨217502665392667593602109221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145001776928445062401406147 217502665392667593602109221)
  ·
    refine ⟨40781749761125173800395479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217502665392667593602109221 40781749761125173800395479)
    ·
      refine ⟨61172624641687760700593219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40781749761125173800395479 61172624641687760700593219)
      ·
        refine ⟨91758936962531641050889829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61172624641687760700593219 91758936962531641050889829)
        ·
          refine ⟨17204800680474682697041843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91758936962531641050889829 17204800680474682697041843)
          ·
            refine ⟨25807201020712024045562765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17204800680474682697041843 25807201020712024045562765)
            ·
              refine ⟨9677700382767009017086037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25807201020712024045562765 9677700382767009017086037)
              ·
                refine ⟨113410551360550886918977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9677700382767009017086037 113410551360550886918977)
                ·
                  rfl

theorem cell23_5963389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 8].length) (baseStart_5963389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963389 prefixEnd_5963389 := by exact prefixLift 5963389
  have htrace : WordTrace (prefixWord ++ tailWord_5963389) baseStart_5963389 baseEnd_5963389 := by
    simpa [prefixWord, tailWord_5963389, baseEnd_5963389] using wordTrace_append hprefix tailTrace_5963389
  have hstable : (prefixWord ++ tailWord_5963389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963389).length < 2 ^ (prefixWord ++ tailWord_5963389).sum := by decide
  have hdescent : baseEnd_5963389 < baseStart_5963389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963406 : List Nat := [4, 1, 1, 3, 1, 3, 3, 7]
def baseStart_5963406 : Nat := 118140960795 + 5963406 * 2 ^ 59
def prefixEnd_5963406 : Nat := 4983230072969 + 3 ^ 40 * 5963406 * 2
def baseEnd_5963406 : Nat := 113410874663185199270363

theorem tailTrace_5963406 : CollatzResearch.WordTrace tailWord_5963406 prefixEnd_5963406 113410874663185199270363 := by
  unfold tailWord_5963406
  simp only [CollatzResearch.WordTrace]
  refine ⟨27187910679200750688184759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145002190289070670336985381 27187910679200750688184759)
  ·
    refine ⟨40781866018801126032277139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27187910679200750688184759 40781866018801126032277139)
    ·
      refine ⟨61172799028201689048415709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40781866018801126032277139 61172799028201689048415709)
      ·
        refine ⟨22939799635575633393155891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61172799028201689048415709 22939799635575633393155891)
        ·
          refine ⟨34409699453363450089733837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22939799635575633393155891 34409699453363450089733837)
          ·
            refine ⟨12903637295011293783650189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34409699453363450089733837 12903637295011293783650189)
            ·
              refine ⟨4838863985629235168868821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12903637295011293783650189 4838863985629235168868821)
              ·
                refine ⟨113410874663185199270363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4838863985629235168868821 113410874663185199270363)
                ·
                  rfl

theorem cell23_5963406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_5963406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963406 prefixEnd_5963406 := by exact prefixLift 5963406
  have htrace : WordTrace (prefixWord ++ tailWord_5963406) baseStart_5963406 baseEnd_5963406 := by
    simpa [prefixWord, tailWord_5963406, baseEnd_5963406] using wordTrace_append hprefix tailTrace_5963406
  have hstable : (prefixWord ++ tailWord_5963406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963406).length < 2 ^ (prefixWord ++ tailWord_5963406).sum := by decide
  have hdescent : baseEnd_5963406 < baseStart_5963406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963416 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_5963416 : Nat := 118140960795 + 5963416 * 2 ^ 59
def prefixEnd_5963416 : Nat := 4983230072969 + 3 ^ 40 * 5963416 * 2
def baseEnd_5963416 : Nat := 3062098750712545341174755

theorem tailTrace_5963416 : CollatzResearch.WordTrace tailWord_5963416 prefixEnd_5963416 3062098750712545341174755 := by
  unfold tailWord_5963416
  simp only [CollatzResearch.WordTrace]
  refine ⟨108751825081784888606671051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145002433442379851475561401 108751825081784888606671051)
  ·
    refine ⟨163127737622677332910006577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108751825081784888606671051 163127737622677332910006577)
    ·
      refine ⟨122345803217007999682504933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163127737622677332910006577 122345803217007999682504933)
      ·
        refine ⟨22939838103188999940469675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122345803217007999682504933 22939838103188999940469675)
        ·
          refine ⟨34409757154783499910704513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22939838103188999940469675 34409757154783499910704513)
          ·
            refine ⟨25807317866087624933028385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34409757154783499910704513 25807317866087624933028385)
            ·
              refine ⟨19355488399565718699771289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25807317866087624933028385 19355488399565718699771289)
              ·
                refine ⟨14516616299674289024828467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19355488399565718699771289 14516616299674289024828467)
                ·
                  refine ⟨21774924449511433537242701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14516616299674289024828467 21774924449511433537242701)
                  ·
                    refine ⟨8165596668566787576466013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21774924449511433537242701 8165596668566787576466013)
                    ·
                      refine ⟨3062098750712545341174755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8165596668566787576466013 3062098750712545341174755)
                      ·
                        rfl

theorem cell23_5963416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_5963416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963416 prefixEnd_5963416 := by exact prefixLift 5963416
  have htrace : WordTrace (prefixWord ++ tailWord_5963416) baseStart_5963416 baseEnd_5963416 := by
    simpa [prefixWord, tailWord_5963416, baseEnd_5963416] using wordTrace_append hprefix tailTrace_5963416
  have hstable : (prefixWord ++ tailWord_5963416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963416).length < 2 ^ (prefixWord ++ tailWord_5963416).sum := by decide
  have hdescent : baseEnd_5963416 < baseStart_5963416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963449 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 2, 6]
def baseStart_5963449 : Nat := 118140960795 + 5963449 * 2 ^ 59
def prefixEnd_5963449 : Nat := 4983230072969 + 3 ^ 40 * 5963449 * 2
def baseEnd_5963449 : Nat := 1020705231858047904020701

theorem tailTrace_5963449 : CollatzResearch.WordTrace tailWord_5963449 prefixEnd_5963449 1020705231858047904020701 := by
  unfold tailWord_5963449
  simp only [CollatzResearch.WordTrace]
  refine ⟨217504853772450223849293401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145003235848300149232862267 217504853772450223849293401)
  ·
    refine ⟨163128640329337667886970051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217504853772450223849293401 163128640329337667886970051)
    ·
      refine ⟨244692960494006501830455077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163128640329337667886970051 244692960494006501830455077)
      ·
        refine ⟨45879930092626219093210327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244692960494006501830455077 45879930092626219093210327)
        ·
          refine ⟨68819895138939328639815491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45879930092626219093210327 68819895138939328639815491)
          ·
            refine ⟨103229842708408992959723237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68819895138939328639815491 103229842708408992959723237)
            ·
              refine ⟨19355595507826686179948107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103229842708408992959723237 19355595507826686179948107)
              ·
                refine ⟨29033393261740029269922161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19355595507826686179948107 29033393261740029269922161)
                ·
                  refine ⟨21775044946305021952441621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29033393261740029269922161 21775044946305021952441621)
                  ·
                    refine ⟨1020705231858047904020701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21775044946305021952441621 1020705231858047904020701)
                    ·
                      rfl

theorem cell23_5963449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_5963449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963449 prefixEnd_5963449 := by exact prefixLift 5963449
  have htrace : WordTrace (prefixWord ++ tailWord_5963449) baseStart_5963449 baseEnd_5963449 := by
    simpa [prefixWord, tailWord_5963449, baseEnd_5963449] using wordTrace_append hprefix tailTrace_5963449
  have hstable : (prefixWord ++ tailWord_5963449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963449).length < 2 ^ (prefixWord ++ tailWord_5963449).sum := by decide
  have hdescent : baseEnd_5963449 < baseStart_5963449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963450 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3]
def baseStart_5963450 : Nat := 118140960795 + 5963450 * 2 ^ 59
def prefixEnd_5963450 : Nat := 4983230072969 + 3 ^ 40 * 5963450 * 2
def baseEnd_5963450 : Nat := 3062116209054798208149599

theorem tailTrace_5963450 : CollatzResearch.WordTrace tailWord_5963450 prefixEnd_5963450 3062116209054798208149599 := by
  unfold tailWord_5963450
  simp only [CollatzResearch.WordTrace]
  refine ⟨54376222561361650255019951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145003260163631067346719869 54376222561361650255019951)
  ·
    refine ⟨81564333842042475382529927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54376222561361650255019951 81564333842042475382529927)
    ·
      refine ⟨122346500763063713073794891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81564333842042475382529927 122346500763063713073794891)
      ·
        refine ⟨183519751144595569610692337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122346500763063713073794891 183519751144595569610692337)
        ·
          refine ⟨137639813358446677208019253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183519751144595569610692337 137639813358446677208019253)
          ·
            refine ⟨12903732502354375988251805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137639813358446677208019253 12903732502354375988251805)
            ·
              refine ⟨4838899688382890995594427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12903732502354375988251805 4838899688382890995594427)
              ·
                refine ⟨7258349532574336493391641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4838899688382890995594427 7258349532574336493391641)
                ·
                  refine ⟨5443762149430752370043731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7258349532574336493391641 5443762149430752370043731)
                  ·
                    refine ⟨8165643224146128555065597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5443762149430752370043731 8165643224146128555065597)
                    ·
                      refine ⟨3062116209054798208149599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8165643224146128555065597 3062116209054798208149599)
                      ·
                        rfl

theorem cell23_5963450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_5963450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963450 prefixEnd_5963450 := by exact prefixLift 5963450
  have htrace : WordTrace (prefixWord ++ tailWord_5963450) baseStart_5963450 baseEnd_5963450 := by
    simpa [prefixWord, tailWord_5963450, baseEnd_5963450] using wordTrace_append hprefix tailTrace_5963450
  have hstable : (prefixWord ++ tailWord_5963450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963450).length < 2 ^ (prefixWord ++ tailWord_5963450).sum := by decide
  have hdescent : baseEnd_5963450 < baseStart_5963450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963460 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_5963460 : Nat := 118140960795 + 5963460 * 2 ^ 59
def prefixEnd_5963460 : Nat := 4983230072969 + 3 ^ 40 * 5963460 * 2
def baseEnd_5963460 : Nat := 3062121343861343169024553

theorem tailTrace_5963460 : CollatzResearch.WordTrace tailWord_5963460 prefixEnd_5963460 3062121343861343169024553 := by
  unfold tailWord_5963460
  simp only [CollatzResearch.WordTrace]
  refine ⟨108752627487705186363971917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145003503316940248485295889 108752627487705186363971917)
  ·
    refine ⟨40782235307889444886489469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108752627487705186363971917 40782235307889444886489469)
    ·
      refine ⟨15293338240458541832433551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40782235307889444886489469 15293338240458541832433551)
      ·
        refine ⟨22940007360687812748650327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15293338240458541832433551 22940007360687812748650327)
        ·
          refine ⟨34410011041031719122975491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22940007360687812748650327 34410011041031719122975491)
          ·
            refine ⟨51615016561547578684463237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34410011041031719122975491 51615016561547578684463237)
            ·
              refine ⟨9677815605290171003336857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51615016561547578684463237 9677815605290171003336857)
              ·
                refine ⟨7258361703967628252502643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9677815605290171003336857 7258361703967628252502643)
                ·
                  refine ⟨10887542555951442378753965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7258361703967628252502643 10887542555951442378753965)
                  ·
                    refine ⟨4082828458481790892032737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10887542555951442378753965 4082828458481790892032737)
                    ·
                      refine ⟨3062121343861343169024553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082828458481790892032737 3062121343861343169024553)
                      ·
                        rfl

theorem cell23_5963460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_5963460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963460 prefixEnd_5963460 := by exact prefixLift 5963460
  have htrace : WordTrace (prefixWord ++ tailWord_5963460) baseStart_5963460 baseEnd_5963460 := by
    simpa [prefixWord, tailWord_5963460, baseEnd_5963460] using wordTrace_append hprefix tailTrace_5963460
  have hstable : (prefixWord ++ tailWord_5963460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963460).length < 2 ^ (prefixWord ++ tailWord_5963460).sum := by decide
  have hdescent : baseEnd_5963460 < baseStart_5963460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963473 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 4, 2, 2]
def baseStart_5963473 : Nat := 118140960795 + 5963473 * 2 ^ 59
def prefixEnd_5963473 : Nat := 4983230072969 + 3 ^ 40 * 5963473 * 2
def baseEnd_5963473 : Nat := 3062128019109851618161993

theorem tailTrace_5963473 : CollatzResearch.WordTrace tailWord_5963473 prefixEnd_5963473 3062128019109851618161993 := by
  unfold tailWord_5963473
  simp only [CollatzResearch.WordTrace]
  refine ⟨217505729124363275948167073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145003819416242183965444715 217505729124363275948167073)
  ·
    refine ⟨163129296843272456961125305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217505729124363275948167073 163129296843272456961125305)
    ·
      refine ⟨122346972632454342720843979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163129296843272456961125305 122346972632454342720843979)
      ·
        refine ⟨183520458948681514081265969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122346972632454342720843979 183520458948681514081265969)
        ·
          refine ⟨137640344211511135560949477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183520458948681514081265969 137640344211511135560949477)
          ·
            refine ⟨25807564539658337917678027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137640344211511135560949477 25807564539658337917678027)
            ·
              refine ⟨38711346809487506876517041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25807564539658337917678027 38711346809487506876517041)
              ·
                refine ⟨29033510107115630157387781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38711346809487506876517041 29033510107115630157387781)
                ·
                  refine ⟨5443783145084180654510209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29033510107115630157387781 5443783145084180654510209)
                  ·
                    refine ⟨4082837358813135490882657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5443783145084180654510209 4082837358813135490882657)
                    ·
                      refine ⟨3062128019109851618161993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082837358813135490882657 3062128019109851618161993)
                      ·
                        rfl

theorem cell23_5963473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_5963473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963473 prefixEnd_5963473 := by exact prefixLift 5963473
  have htrace : WordTrace (prefixWord ++ tailWord_5963473) baseStart_5963473 baseEnd_5963473 := by
    simpa [prefixWord, tailWord_5963473, baseEnd_5963473] using wordTrace_append hprefix tailTrace_5963473
  have hstable : (prefixWord ++ tailWord_5963473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963473).length < 2 ^ (prefixWord ++ tailWord_5963473).sum := by decide
  have hdescent : baseEnd_5963473 < baseStart_5963473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963476 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5963476 : Nat := 118140960795 + 5963476 * 2 ^ 59
def prefixEnd_5963476 : Nat := 4983230072969 + 3 ^ 40 * 5963476 * 2
def baseEnd_5963476 : Nat := 3062129559551815106424479

theorem tailTrace_5963476 : CollatzResearch.WordTrace tailWord_5963476 prefixEnd_5963476 3062129559551815106424479 := by
  unfold tailWord_5963476
  simp only [CollatzResearch.WordTrace]
  refine ⟨108752919271676203730263141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145003892362234938307017521 108752919271676203730263141)
  ·
    refine ⟨20391172363439288199424339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108752919271676203730263141 20391172363439288199424339)
    ·
      refine ⟨30586758545158932299136509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20391172363439288199424339 30586758545158932299136509)
      ·
        refine ⟨11470034454434599612176191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30586758545158932299136509 11470034454434599612176191)
        ·
          refine ⟨17205051681651899418264287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11470034454434599612176191 17205051681651899418264287)
          ·
            refine ⟨25807577522477849127396431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17205051681651899418264287 25807577522477849127396431)
            ·
              refine ⟨38711366283716773691094647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25807577522477849127396431 38711366283716773691094647)
              ·
                refine ⟨58067049425575160536641971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38711366283716773691094647 58067049425575160536641971)
                ·
                  refine ⟨87100574138362740804962957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58067049425575160536641971 87100574138362740804962957)
                  ·
                    refine ⟨32662715301886027801861109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87100574138362740804962957 32662715301886027801861109)
                    ·
                      refine ⟨3062129559551815106424479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32662715301886027801861109 3062129559551815106424479)
                      ·
                        rfl

theorem cell23_5963476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5963476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963476 prefixEnd_5963476 := by exact prefixLift 5963476
  have htrace : WordTrace (prefixWord ++ tailWord_5963476) baseStart_5963476 baseEnd_5963476 := by
    simpa [prefixWord, tailWord_5963476, baseEnd_5963476] using wordTrace_append hprefix tailTrace_5963476
  have hstable : (prefixWord ++ tailWord_5963476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963476).length < 2 ^ (prefixWord ++ tailWord_5963476).sum := by decide
  have hdescent : baseEnd_5963476 < baseStart_5963476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963496 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 7]
def baseStart_5963496 : Nat := 118140960795 + 5963496 * 2 ^ 59
def prefixEnd_5963496 : Nat := 4983230072969 + 3 ^ 40 * 5963496 * 2
def baseEnd_5963496 : Nat := 340237758796100558686043

theorem tailTrace_5963496 : CollatzResearch.WordTrace tailWord_5963496 prefixEnd_5963496 340237758796100558686043 := by
  unfold tailWord_5963496
  simp only [CollatzResearch.WordTrace]
  refine ⟨108753284001639975438127171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145004378668853300584169561 108753284001639975438127171)
  ·
    refine ⟨163129926002459963157190757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108753284001639975438127171 163129926002459963157190757)
    ·
      refine ⟨30586861125461243091973267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163129926002459963157190757 30586861125461243091973267)
      ·
        refine ⟨45880291688191864637959901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30586861125461243091973267 45880291688191864637959901)
        ·
          refine ⟨17205109383071949239234963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45880291688191864637959901 17205109383071949239234963)
          ·
            refine ⟨25807664074607923858852445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17205109383071949239234963 25807664074607923858852445)
            ·
              refine ⟨9677874027977971447069667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25807664074607923858852445 9677874027977971447069667)
              ·
                refine ⟨14516811041966957170604501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9677874027977971447069667 14516811041966957170604501)
                ·
                  refine ⟨340237758796100558686043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14516811041966957170604501 340237758796100558686043)
                  ·
                    rfl

theorem cell23_5963496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 7].length) (baseStart_5963496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963496 prefixEnd_5963496 := by exact prefixLift 5963496
  have htrace : WordTrace (prefixWord ++ tailWord_5963496) baseStart_5963496 baseEnd_5963496 := by
    simpa [prefixWord, tailWord_5963496, baseEnd_5963496] using wordTrace_append hprefix tailTrace_5963496
  have hstable : (prefixWord ++ tailWord_5963496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963496).length < 2 ^ (prefixWord ++ tailWord_5963496).sum := by decide
  have hdescent : baseEnd_5963496 < baseStart_5963496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963506 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_5963506 : Nat := 118140960795 + 5963506 * 2 ^ 59
def prefixEnd_5963506 : Nat := 4983230072969 + 3 ^ 40 * 5963506 * 2
def baseEnd_5963506 : Nat := 3062144963971449989049341

theorem tailTrace_5963506 : CollatzResearch.WordTrace tailWord_5963506 prefixEnd_5963506 3062144963971449989049341 := by
  unfold tailWord_5963506
  simp only [CollatzResearch.WordTrace]
  refine ⟨54376733183310930646029593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145004621822162481722745581 54376733183310930646029593)
  ·
    refine ⟨40782549887483197984522195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54376733183310930646029593 40782549887483197984522195)
    ·
      refine ⟨61173824831224796976783293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40782549887483197984522195 61173824831224796976783293)
      ·
        refine ⟨22940184311709298866293735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61173824831224796976783293 22940184311709298866293735)
        ·
          refine ⟨34410276467563948299440603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22940184311709298866293735 34410276467563948299440603)
          ·
            refine ⟨51615414701345922449160905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34410276467563948299440603 51615414701345922449160905)
            ·
              refine ⟨38711561026009441836870679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51615414701345922449160905 38711561026009441836870679)
              ·
                refine ⟨58067341539014162755306019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38711561026009441836870679 58067341539014162755306019)
                ·
                  refine ⟨87101012308521244132959029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58067341539014162755306019 87101012308521244132959029)
                  ·
                    refine ⟨8165719903923866637464909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87101012308521244132959029 8165719903923866637464909)
                    ·
                      refine ⟨3062144963971449989049341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8165719903923866637464909 3062144963971449989049341)
                      ·
                        rfl

theorem cell23_5963506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_5963506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963506 prefixEnd_5963506 := by exact prefixLift 5963506
  have htrace : WordTrace (prefixWord ++ tailWord_5963506) baseStart_5963506 baseEnd_5963506 := by
    simpa [prefixWord, tailWord_5963506, baseEnd_5963506] using wordTrace_append hprefix tailTrace_5963506
  have hstable : (prefixWord ++ tailWord_5963506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963506).length < 2 ^ (prefixWord ++ tailWord_5963506).sum := by decide
  have hdescent : baseEnd_5963506 < baseStart_5963506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963577 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 2, 5]
def baseStart_5963577 : Nat := 118140960795 + 5963577 * 2 ^ 59
def prefixEnd_5963577 : Nat := 4983230072969 + 3 ^ 40 * 5963577 * 2
def baseEnd_5963577 : Nat := 1020727140365973070420505

theorem tailTrace_5963577 : CollatzResearch.WordTrace tailWord_5963577 prefixEnd_5963577 1020727140365973070420505 := by
  unfold tailWord_5963577
  simp only [CollatzResearch.WordTrace]
  refine ⟨217509522315986501709952985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145006348210657667806635323 217509522315986501709952985)
  ·
    refine ⟨163132141736989876282464739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217509522315986501709952985 163132141736989876282464739)
    ·
      refine ⟨244698212605484814423697109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163132141736989876282464739 244698212605484814423697109)
      ·
        refine ⟨5735114357941050338055401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 244698212605484814423697109 5735114357941050338055401)
        ·
          refine ⟨4301335768455787753541551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735114357941050338055401 4301335768455787753541551)
          ·
            refine ⟨6452003652683681630312327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301335768455787753541551 6452003652683681630312327)
            ·
              refine ⟨9678005479025522445468491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452003652683681630312327 9678005479025522445468491)
              ·
                refine ⟨14517008218538283668202737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9678005479025522445468491 14517008218538283668202737)
                ·
                  refine ⟨10887756163903712751152053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14517008218538283668202737 10887756163903712751152053)
                  ·
                    refine ⟨1020727140365973070420505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10887756163903712751152053 1020727140365973070420505)
                    ·
                      rfl

theorem cell23_5963577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 5].length) (baseStart_5963577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963577 prefixEnd_5963577 := by exact prefixLift 5963577
  have htrace : WordTrace (prefixWord ++ tailWord_5963577) baseStart_5963577 baseEnd_5963577 := by
    simpa [prefixWord, tailWord_5963577, baseEnd_5963577] using wordTrace_append hprefix tailTrace_5963577
  have hstable : (prefixWord ++ tailWord_5963577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963577).length < 2 ^ (prefixWord ++ tailWord_5963577).sum := by decide
  have hdescent : baseEnd_5963577 < baseStart_5963577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963583 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 3]
def baseStart_5963583 : Nat := 118140960795 + 5963583 * 2 ^ 59
def prefixEnd_5963583 : Nat := 4983230072969 + 3 ^ 40 * 5963583 * 2
def baseEnd_5963583 : Nat := 3062184501981846187786487

theorem tailTrace_5963583 : CollatzResearch.WordTrace tailWord_5963583 prefixEnd_5963583 3062184501981846187786487 := by
  unfold tailWord_5963583
  simp only [CollatzResearch.WordTrace]
  refine ⟨217509741153964764734671403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145006494102643176489780935 217509741153964764734671403)
  ·
    refine ⟨326264611730947147102007105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217509741153964764734671403 326264611730947147102007105)
    ·
      refine ⟨244698458798210360326505329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326264611730947147102007105 244698458798210360326505329)
      ·
        refine ⟨183523844098657770244878997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244698458798210360326505329 183523844098657770244878997)
        ·
          refine ⟨8602680192124582980228703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 183523844098657770244878997 8602680192124582980228703)
          ·
            refine ⟨12904020288186874470343055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8602680192124582980228703 12904020288186874470343055)
            ·
              refine ⟨19356030432280311705514583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12904020288186874470343055 19356030432280311705514583)
              ·
                refine ⟨29034045648420467558271875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19356030432280311705514583 29034045648420467558271875)
                ·
                  refine ⟨43551068472630701337407813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29034045648420467558271875 43551068472630701337407813)
                  ·
                    refine ⟨8165825338618256500763965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43551068472630701337407813 8165825338618256500763965)
                    ·
                      refine ⟨3062184501981846187786487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8165825338618256500763965 3062184501981846187786487)
                      ·
                        rfl

theorem cell23_5963583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_5963583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963583 prefixEnd_5963583 := by exact prefixLift 5963583
  have htrace : WordTrace (prefixWord ++ tailWord_5963583) baseStart_5963583 baseEnd_5963583 := by
    simpa [prefixWord, tailWord_5963583, baseEnd_5963583] using wordTrace_append hprefix tailTrace_5963583
  have hstable : (prefixWord ++ tailWord_5963583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963583).length < 2 ^ (prefixWord ++ tailWord_5963583).sum := by decide
  have hdescent : baseEnd_5963583 < baseStart_5963583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963620 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 6]
def baseStart_5963620 : Nat := 118140960795 + 5963620 * 2 ^ 59
def prefixEnd_5963620 : Nat := 4983230072969 + 3 ^ 40 * 5963620 * 2
def baseEnd_5963620 : Nat := 340244833418451393669313

theorem tailTrace_5963620 : CollatzResearch.WordTrace tailWord_5963620 prefixEnd_5963620 340244833418451393669313 := by
  unfold tailWord_5963620
  simp only [CollatzResearch.WordTrace]
  refine ⟨108755545327415360026884157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145007393769887146702512209 108755545327415360026884157)
  ·
    refine ⟨40783329497780760010081559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108755545327415360026884157 40783329497780760010081559)
    ·
      refine ⟨61174994246671140015122339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40783329497780760010081559 61174994246671140015122339)
      ·
        refine ⟨91762491370006710022683509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61174994246671140015122339 91762491370006710022683509)
        ·
          refine ⟨8602733565938129064626579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91762491370006710022683509 8602733565938129064626579)
          ·
            refine ⟨12904100348907193596939869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8602733565938129064626579 12904100348907193596939869)
            ·
              refine ⟨4839037630840197598852451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12904100348907193596939869 4839037630840197598852451)
              ·
                refine ⟨7258556446260296398278677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839037630840197598852451 7258556446260296398278677)
                ·
                  refine ⟨340244833418451393669313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7258556446260296398278677 340244833418451393669313)
                  ·
                    rfl

theorem cell23_5963620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_5963620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963620 prefixEnd_5963620 := by exact prefixLift 5963620
  have htrace : WordTrace (prefixWord ++ tailWord_5963620) baseStart_5963620 baseEnd_5963620 := by
    simpa [prefixWord, tailWord_5963620, baseEnd_5963620] using wordTrace_append hprefix tailTrace_5963620
  have hstable : (prefixWord ++ tailWord_5963620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963620).length < 2 ^ (prefixWord ++ tailWord_5963620).sum := by decide
  have hdescent : baseEnd_5963620 < baseStart_5963620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963623 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_5963623 : Nat := 118140960795 + 5963623 * 2 ^ 59
def prefixEnd_5963623 : Nat := 4983230072969 + 3 ^ 40 * 5963623 * 2
def baseEnd_5963623 : Nat := 3062205041208026031286303

theorem tailTrace_5963623 : CollatzResearch.WordTrace tailWord_5963623 prefixEnd_5963623 3062205041208026031286303 := by
  unfold tailWord_5963623
  simp only [CollatzResearch.WordTrace]
  refine ⟨217511200073819851566127523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145007466715879901044085015 217511200073819851566127523)
  ·
    refine ⟨326266800110729777349191285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217511200073819851566127523 326266800110729777349191285)
    ·
      refine ⟨30587512510380916626486683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326266800110729777349191285 30587512510380916626486683)
      ·
        refine ⟨45881268765571374939730025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30587512510380916626486683 45881268765571374939730025)
        ·
          refine ⟨34410951574178531204797519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45881268765571374939730025 34410951574178531204797519)
          ·
            refine ⟨51616427361267796807196279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34410951574178531204797519 51616427361267796807196279)
            ·
              refine ⟨77424641041901695210794419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51616427361267796807196279 77424641041901695210794419)
              ·
                refine ⟨116136961562852542816191629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77424641041901695210794419 116136961562852542816191629)
                ·
                  refine ⟨43551360586069703556071861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116136961562852542816191629 43551360586069703556071861)
                  ·
                    refine ⟨4082940054944034708381737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43551360586069703556071861 4082940054944034708381737)
                    ·
                      refine ⟨3062205041208026031286303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4082940054944034708381737 3062205041208026031286303)
                      ·
                        rfl

theorem cell23_5963623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_5963623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963623 prefixEnd_5963623 := by exact prefixLift 5963623
  have htrace : WordTrace (prefixWord ++ tailWord_5963623) baseStart_5963623 baseEnd_5963623 := by
    simpa [prefixWord, tailWord_5963623, baseEnd_5963623] using wordTrace_append hprefix tailTrace_5963623
  have hstable : (prefixWord ++ tailWord_5963623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963623).length < 2 ^ (prefixWord ++ tailWord_5963623).sum := by decide
  have hdescent : baseEnd_5963623 < baseStart_5963623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
