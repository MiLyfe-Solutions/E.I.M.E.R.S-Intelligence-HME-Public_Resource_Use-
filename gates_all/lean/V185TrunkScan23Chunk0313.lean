import V185TrunkScan23Chunk0312

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1851669 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_1851669 : Nat := 118140960795 + 1851669 * 2 ^ 59
def prefixEnd_1851669 : Nat := 4983230072969 + 3 ^ 40 * 1851669 * 2
def baseEnd_1851669 : Nat := 316932070010073690073945

theorem tailTrace_1851669 : CollatzResearch.WordTrace tailWord_1851669 prefixEnd_1851669 316932070010073690073945 := by
  unfold tailWord_1851669
  simp only [CollatzResearch.WordTrace]
  refine ⟨67535916728726927733166061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45023944485817951822110707 67535916728726927733166061)
  ·
    refine ⟨25325968773272597899937273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67535916728726927733166061 25325968773272597899937273)
    ·
      refine ⟨18994476579954448424952955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25325968773272597899937273 18994476579954448424952955)
      ·
        refine ⟨28491714869931672637429433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18994476579954448424952955 28491714869931672637429433)
        ·
          refine ⟨21368786152448754478072075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28491714869931672637429433 21368786152448754478072075)
          ·
            refine ⟨32053179228673131717108113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21368786152448754478072075 32053179228673131717108113)
            ·
              refine ⟨24039884421504848787831085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32053179228673131717108113 24039884421504848787831085)
              ·
                refine ⟨9014956658064318295436657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24039884421504848787831085 9014956658064318295436657)
                ·
                  refine ⟨6761217493548238721577493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9014956658064318295436657 6761217493548238721577493)
                  ·
                    refine ⟨316932070010073690073945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6761217493548238721577493 316932070010073690073945)
                    ·
                      rfl

theorem cell23_1851669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_1851669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851669 prefixEnd_1851669 := by exact prefixLift 1851669
  have htrace : WordTrace (prefixWord ++ tailWord_1851669) baseStart_1851669 baseEnd_1851669 := by
    simpa [prefixWord, tailWord_1851669, baseEnd_1851669] using wordTrace_append hprefix tailTrace_1851669
  have hstable : (prefixWord ++ tailWord_1851669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851669).length < 2 ^ (prefixWord ++ tailWord_1851669).sum := by decide
  have hdescent : baseEnd_1851669 < baseStart_1851669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851680 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 1, 3, 2]
def baseStart_1851680 : Nat := 118140960795 + 1851680 * 2 ^ 59
def prefixEnd_1851680 : Nat := 4983230072969 + 3 ^ 40 * 1851680 * 2
def baseEnd_1851680 : Nat := 950801858317420527184285

theorem tailTrace_1851680 : CollatzResearch.WordTrace tailWord_1851680 prefixEnd_1851680 950801858317420527184285 := by
  unfold tailWord_1851680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33768158965843538305908247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45024211954458051074544329 33768158965843538305908247)
  ·
    refine ⟨50652238448765307458862371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33768158965843538305908247 50652238448765307458862371)
    ·
      refine ⟨75978357673147961188293557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50652238448765307458862371 75978357673147961188293557)
      ·
        refine ⟨7122971031857621361402521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75978357673147961188293557 7122971031857621361402521)
        ·
          refine ⟨5342228273893216021051891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7122971031857621361402521 5342228273893216021051891)
          ·
            refine ⟨8013342410839824031577837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342228273893216021051891 8013342410839824031577837)
            ·
              refine ⟨3005003404064934011841689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8013342410839824031577837 3005003404064934011841689)
              ·
                refine ⟨2253752553048700508881267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005003404064934011841689 2253752553048700508881267)
                ·
                  refine ⟨3380628829573050763321901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253752553048700508881267 3380628829573050763321901)
                  ·
                    refine ⟨1267735811089894036245713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380628829573050763321901 1267735811089894036245713)
                    ·
                      refine ⟨950801858317420527184285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267735811089894036245713 950801858317420527184285)
                      ·
                        rfl

theorem cell23_1851680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_1851680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851680 prefixEnd_1851680 := by exact prefixLift 1851680
  have htrace : WordTrace (prefixWord ++ tailWord_1851680) baseStart_1851680 baseEnd_1851680 := by
    simpa [prefixWord, tailWord_1851680, baseEnd_1851680] using wordTrace_append hprefix tailTrace_1851680
  have hstable : (prefixWord ++ tailWord_1851680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851680).length < 2 ^ (prefixWord ++ tailWord_1851680).sum := by decide
  have hdescent : baseEnd_1851680 < baseStart_1851680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851687 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1851687 : Nat := 118140960795 + 1851687 * 2 ^ 59
def prefixEnd_1851687 : Nat := 4983230072969 + 3 ^ 40 * 1851687 * 2
def baseEnd_1851687 : Nat := 950805452682001999796753

theorem tailTrace_1851687 : CollatzResearch.WordTrace tailWord_1851687 prefixEnd_1851687 950805452682001999796753 := by
  unfold tailWord_1851687
  simp only [CollatzResearch.WordTrace]
  refine ⟨67536573242661716807321315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45024382161774477871547543 67536573242661716807321315)
  ·
    refine ⟨101304859863992575210981973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67536573242661716807321315 101304859863992575210981973)
    ·
      refine ⟨1187166326531162990753695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 101304859863992575210981973 1187166326531162990753695)
      ·
        refine ⟨1780749489796744486130543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187166326531162990753695 1780749489796744486130543)
        ·
          refine ⟨2671124234695116729195815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780749489796744486130543 2671124234695116729195815)
          ·
            refine ⟨4006686352042675093793723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671124234695116729195815 4006686352042675093793723)
            ·
              refine ⟨6010029528064012640690585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006686352042675093793723 6010029528064012640690585)
              ·
                refine ⟨4507522146048009480517939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010029528064012640690585 4507522146048009480517939)
                ·
                  refine ⟨6761283219072014220776909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4507522146048009480517939 6761283219072014220776909)
                  ·
                    refine ⟨2535481207152005332791341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6761283219072014220776909 2535481207152005332791341)
                    ·
                      refine ⟨950805452682001999796753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2535481207152005332791341 950805452682001999796753)
                      ·
                        rfl

theorem cell23_1851687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1851687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851687 prefixEnd_1851687 := by exact prefixLift 1851687
  have htrace : WordTrace (prefixWord ++ tailWord_1851687) baseStart_1851687 baseEnd_1851687 := by
    simpa [prefixWord, tailWord_1851687, baseEnd_1851687] using wordTrace_append hprefix tailTrace_1851687
  have hstable : (prefixWord ++ tailWord_1851687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851687).length < 2 ^ (prefixWord ++ tailWord_1851687).sum := by decide
  have hdescent : baseEnd_1851687 < baseStart_1851687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851697 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 1, 3, 2]
def baseStart_1851697 : Nat := 118140960795 + 1851697 * 2 ^ 59
def prefixEnd_1851697 : Nat := 4983230072969 + 3 ^ 40 * 1851697 * 2
def baseEnd_1851697 : Nat := 950810587488546960671707

theorem tailTrace_1851697 : CollatzResearch.WordTrace tailWord_1851697 prefixEnd_1851697 950810587488546960671707 := by
  unfold tailWord_1851697
  simp only [CollatzResearch.WordTrace]
  refine ⟨67536937972625488515185345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45024625315083659010123563 67536937972625488515185345)
  ·
    refine ⟨50652703479469116386389009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67536937972625488515185345 50652703479469116386389009)
    ·
      refine ⟨37989527609601837289791757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50652703479469116386389009 37989527609601837289791757)
      ·
        refine ⟨14246072853600688983671909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37989527609601837289791757 14246072853600688983671909)
        ·
          refine ⟨2671138660050129184438483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14246072853600688983671909 2671138660050129184438483)
          ·
            refine ⟨4006707990075193776657725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671138660050129184438483 4006707990075193776657725)
            ·
              refine ⟨1502515496278197666246647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4006707990075193776657725 1502515496278197666246647)
              ·
                refine ⟨2253773244417296499369971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502515496278197666246647 2253773244417296499369971)
                ·
                  refine ⟨3380659866625944749054957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253773244417296499369971 3380659866625944749054957)
                  ·
                    refine ⟨1267747449984729280895609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380659866625944749054957 1267747449984729280895609)
                    ·
                      refine ⟨950810587488546960671707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267747449984729280895609 950810587488546960671707)
                      ·
                        rfl

theorem cell23_1851697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_1851697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851697 prefixEnd_1851697 := by exact prefixLift 1851697
  have htrace : WordTrace (prefixWord ++ tailWord_1851697) baseStart_1851697 baseEnd_1851697 := by
    simpa [prefixWord, tailWord_1851697, baseEnd_1851697] using wordTrace_append hprefix tailTrace_1851697
  have hstable : (prefixWord ++ tailWord_1851697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851697).length < 2 ^ (prefixWord ++ tailWord_1851697).sum := by decide
  have hdescent : baseEnd_1851697 < baseStart_1851697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851783 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 2, 4, 2]
def baseStart_1851783 : Nat := 118140960795 + 1851783 * 2 ^ 59
def prefixEnd_1851783 : Nat := 4983230072969 + 3 ^ 40 * 1851783 * 2
def baseEnd_1851783 : Nat := 950854746824833624196311

theorem tailTrace_1851783 : CollatzResearch.WordTrace tailWord_1851783 prefixEnd_1851783 950854746824833624196311 := by
  unfold tailWord_1851783
  simp only [CollatzResearch.WordTrace]
  refine ⟨67540074650313925202816003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45026716433542616801877335 67540074650313925202816003)
  ·
    refine ⟨101310111975470887804224005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67540074650313925202816003 101310111975470887804224005)
    ·
      refine ⟨18995645995400791463292001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101310111975470887804224005 18995645995400791463292001)
      ·
        refine ⟨14246734496550593597469001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18995645995400791463292001 14246734496550593597469001)
        ·
          refine ⟨10685050872412945198101751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14246734496550593597469001 10685050872412945198101751)
          ·
            refine ⟨16027576308619417797152627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685050872412945198101751 16027576308619417797152627)
            ·
              refine ⟨24041364462929126695728941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16027576308619417797152627 24041364462929126695728941)
              ·
                refine ⟨9015511673598422510898353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24041364462929126695728941 9015511673598422510898353)
                ·
                  refine ⟨6761633755198816883173765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9015511673598422510898353 6761633755198816883173765)
                  ·
                    refine ⟨1267806329099778165595081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6761633755198816883173765 1267806329099778165595081)
                    ·
                      refine ⟨950854746824833624196311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267806329099778165595081 950854746824833624196311)
                      ·
                        rfl

theorem cell23_1851783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_1851783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851783 prefixEnd_1851783 := by exact prefixLift 1851783
  have htrace : WordTrace (prefixWord ++ tailWord_1851783) baseStart_1851783 baseEnd_1851783 := by
    simpa [prefixWord, tailWord_1851783, baseEnd_1851783] using wordTrace_append hprefix tailTrace_1851783
  have hstable : (prefixWord ++ tailWord_1851783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851783).length < 2 ^ (prefixWord ++ tailWord_1851783).sum := by decide
  have hdescent : baseEnd_1851783 < baseStart_1851783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851843 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 6, 3, 2]
def baseStart_1851843 : Nat := 118140960795 + 1851843 * 2 ^ 59
def prefixEnd_1851843 : Nat := 4983230072969 + 3 ^ 40 * 1851843 * 2
def baseEnd_1851843 : Nat := 950885555664103389446035

theorem tailTrace_1851843 : CollatzResearch.WordTrace tailWord_1851843 prefixEnd_1851843 950885555664103389446035 := by
  unfold tailWord_1851843
  simp only [CollatzResearch.WordTrace]
  refine ⟨67542263030096555450000183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45028175353397703633333455 67542263030096555450000183)
  ·
    refine ⟨101313394545144833175000275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67542263030096555450000183 101313394545144833175000275)
    ·
      refine ⟨151970091817717249762500413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101313394545144833175000275 151970091817717249762500413)
      ·
        refine ⟨56988784431643968660937655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151970091817717249762500413 56988784431643968660937655)
        ·
          refine ⟨85483176647465952991406483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56988784431643968660937655 85483176647465952991406483)
          ·
            refine ⟨128224764971198929487109725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85483176647465952991406483 128224764971198929487109725)
            ·
              refine ⟨48084286864199598557666147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128224764971198929487109725 48084286864199598557666147)
              ·
                refine ⟨72126430296299397836499221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48084286864199598557666147 72126430296299397836499221)
                ·
                  refine ⟨3380926420139034273585901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72126430296299397836499221 3380926420139034273585901)
                  ·
                    refine ⟨1267847407552137852594713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3380926420139034273585901 1267847407552137852594713)
                    ·
                      refine ⟨950885555664103389446035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267847407552137852594713 950885555664103389446035)
                      ·
                        rfl

theorem cell23_1851843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_1851843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851843 prefixEnd_1851843 := by exact prefixLift 1851843
  have htrace : WordTrace (prefixWord ++ tailWord_1851843) baseStart_1851843 baseEnd_1851843 := by
    simpa [prefixWord, tailWord_1851843, baseEnd_1851843] using wordTrace_append hprefix tailTrace_1851843
  have hstable : (prefixWord ++ tailWord_1851843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851843).length < 2 ^ (prefixWord ++ tailWord_1851843).sum := by decide
  have hdescent : baseEnd_1851843 < baseStart_1851843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851903 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 4]
def baseStart_1851903 : Nat := 118140960795 + 1851903 * 2 ^ 59
def prefixEnd_1851903 : Nat := 4983230072969 + 3 ^ 40 * 1851903 * 2
def baseEnd_1851903 : Nat := 950916364503373154695759

theorem tailTrace_1851903 : CollatzResearch.WordTrace tailWord_1851903 prefixEnd_1851903 950916364503373154695759 := by
  unfold tailWord_1851903
  simp only [CollatzResearch.WordTrace]
  refine ⟨67544451409879185697184363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45029634273252790464789575 67544451409879185697184363)
  ·
    refine ⟨101316677114818778545776545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67544451409879185697184363 101316677114818778545776545)
    ·
      refine ⟨75987507836114083909332409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101316677114818778545776545 75987507836114083909332409)
      ·
        refine ⟨56990630877085562931999307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75987507836114083909332409 56990630877085562931999307)
        ·
          refine ⟨85485946315628344397998961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56990630877085562931999307 85485946315628344397998961)
          ·
            refine ⟨64114459736721258298499221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85485946315628344397998961 64114459736721258298499221)
            ·
              refine ⟨3005365300158808982742151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64114459736721258298499221 3005365300158808982742151)
              ·
                refine ⟨4508047950238213474113227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005365300158808982742151 4508047950238213474113227)
                ·
                  refine ⟨6762071925357320211169841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508047950238213474113227 6762071925357320211169841)
                  ·
                    refine ⟨5071553944017990158377381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6762071925357320211169841 5071553944017990158377381)
                    ·
                      refine ⟨950916364503373154695759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5071553944017990158377381 950916364503373154695759)
                      ·
                        rfl

theorem cell23_1851903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_1851903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851903 prefixEnd_1851903 := by exact prefixLift 1851903
  have htrace : WordTrace (prefixWord ++ tailWord_1851903) baseStart_1851903 baseEnd_1851903 := by
    simpa [prefixWord, tailWord_1851903, baseEnd_1851903] using wordTrace_append hprefix tailTrace_1851903
  have hstable : (prefixWord ++ tailWord_1851903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851903).length < 2 ^ (prefixWord ++ tailWord_1851903).sum := by decide
  have hdescent : baseEnd_1851903 < baseStart_1851903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851917 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1851917 : Nat := 118140960795 + 1851917 * 2 ^ 59
def prefixEnd_1851917 : Nat := 4983230072969 + 3 ^ 40 * 1851917 * 2
def baseEnd_1851917 : Nat := 316974517744178699973565

theorem tailTrace_1851917 : CollatzResearch.WordTrace tailWord_1851917 prefixEnd_1851917 316974517744178699973565 := by
  unfold tailWord_1851917
  simp only [CollatzResearch.WordTrace]
  refine ⟨67544962031828466088194005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45029974687885644058796003 67544962031828466088194005)
  ·
    refine ⟨1583085047620979673942047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 67544962031828466088194005 1583085047620979673942047)
    ·
      refine ⟨2374627571431469510913071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583085047620979673942047 2374627571431469510913071)
      ·
        refine ⟨3561941357147204266369607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374627571431469510913071 3561941357147204266369607)
        ·
          refine ⟨5342912035720806399554411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561941357147204266369607 5342912035720806399554411)
          ·
            refine ⟨8014368053581209599331617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342912035720806399554411 8014368053581209599331617)
            ·
              refine ⟨6010776040185907199498713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014368053581209599331617 6010776040185907199498713)
              ·
                refine ⟨4508082030139430399624035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010776040185907199498713 4508082030139430399624035)
                ·
                  refine ⟨6762123045209145599436053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508082030139430399624035 6762123045209145599436053)
                  ·
                    refine ⟨316974517744178699973565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6762123045209145599436053 316974517744178699973565)
                    ·
                      rfl

theorem cell23_1851917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1851917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851917 prefixEnd_1851917 := by exact prefixLift 1851917
  have htrace : WordTrace (prefixWord ++ tailWord_1851917) baseStart_1851917 baseEnd_1851917 := by
    simpa [prefixWord, tailWord_1851917, baseEnd_1851917] using wordTrace_append hprefix tailTrace_1851917
  have hstable : (prefixWord ++ tailWord_1851917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851917).length < 2 ^ (prefixWord ++ tailWord_1851917).sum := by decide
  have hdescent : baseEnd_1851917 < baseStart_1851917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851923 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 3]
def baseStart_1851923 : Nat := 118140960795 + 1851923 * 2 ^ 59
def prefixEnd_1851923 : Nat := 4983230072969 + 3 ^ 40 * 1851923 * 2
def baseEnd_1851923 : Nat := 950926634116463076445667

theorem tailTrace_1851923 : CollatzResearch.WordTrace tailWord_1851923 prefixEnd_1851923 950926634116463076445667 := by
  unfold tailWord_1851923
  simp only [CollatzResearch.WordTrace]
  refine ⟨67545180869806729112912423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45030120579871152741941615 67545180869806729112912423)
  ·
    refine ⟨101317771304710093669368635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67545180869806729112912423 101317771304710093669368635)
    ·
      refine ⟨151976656957065140504052953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101317771304710093669368635 151976656957065140504052953)
      ·
        refine ⟨113982492717798855378039715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151976656957065140504052953 113982492717798855378039715)
        ·
          refine ⟨170973739076698283067059573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113982492717798855378039715 170973739076698283067059573)
          ·
            refine ⟨16028788038440464037536835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170973739076698283067059573 16028788038440464037536835)
            ·
              refine ⟨24043182057660696056305253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16028788038440464037536835 24043182057660696056305253)
              ·
                refine ⟨4508096635811380510557235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24043182057660696056305253 4508096635811380510557235)
                ·
                  refine ⟨6762144953717070765835853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508096635811380510557235 6762144953717070765835853)
                  ·
                    refine ⟨2535804357643901537188445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6762144953717070765835853 2535804357643901537188445)
                    ·
                      refine ⟨950926634116463076445667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2535804357643901537188445 950926634116463076445667)
                      ·
                        rfl

theorem cell23_1851923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_1851923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851923 prefixEnd_1851923 := by exact prefixLift 1851923
  have htrace : WordTrace (prefixWord ++ tailWord_1851923) baseStart_1851923 baseEnd_1851923 := by
    simpa [prefixWord, tailWord_1851923, baseEnd_1851923] using wordTrace_append hprefix tailTrace_1851923
  have hstable : (prefixWord ++ tailWord_1851923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851923).length < 2 ^ (prefixWord ++ tailWord_1851923).sum := by decide
  have hdescent : baseEnd_1851923 < baseStart_1851923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851924 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_1851924 : Nat := 118140960795 + 1851924 * 2 ^ 59
def prefixEnd_1851924 : Nat := 4983230072969 + 3 ^ 40 * 1851924 * 2
def baseEnd_1851924 : Nat := 950927147597117572533163

theorem tailTrace_1851924 : CollatzResearch.WordTrace tailWord_1851924 prefixEnd_1851924 950927147597117572533163 := by
  unfold tailWord_1851924
  simp only [CollatzResearch.WordTrace]
  refine ⟨33772608671401553141849413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45030144895202070855799217 33772608671401553141849413)
  ·
    refine ⟨6332364125887791214096765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33772608671401553141849413 6332364125887791214096765)
    ·
      refine ⟨2374636547207921705286287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6332364125887791214096765 2374636547207921705286287)
      ·
        refine ⟨3561954820811882557929431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374636547207921705286287 3561954820811882557929431)
        ·
          refine ⟨5342932231217823836894147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561954820811882557929431 5342932231217823836894147)
          ·
            refine ⟨8014398346826735755341221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342932231217823836894147 8014398346826735755341221)
            ·
              refine ⟨1502699690030012954126479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8014398346826735755341221 1502699690030012954126479)
              ·
                refine ⟨2254049535045019431189719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502699690030012954126479 2254049535045019431189719)
                ·
                  refine ⟨3381074302567529146784579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254049535045019431189719 3381074302567529146784579)
                  ·
                    refine ⟨5071611453851293720176869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3381074302567529146784579 5071611453851293720176869)
                    ·
                      refine ⟨950927147597117572533163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5071611453851293720176869 950927147597117572533163)
                      ·
                        rfl

theorem cell23_1851924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_1851924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851924 prefixEnd_1851924 := by exact prefixLift 1851924
  have htrace : WordTrace (prefixWord ++ tailWord_1851924) baseStart_1851924 baseEnd_1851924 := by
    simpa [prefixWord, tailWord_1851924, baseEnd_1851924] using wordTrace_append hprefix tailTrace_1851924
  have hstable : (prefixWord ++ tailWord_1851924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851924).length < 2 ^ (prefixWord ++ tailWord_1851924).sum := by decide
  have hdescent : baseEnd_1851924 < baseStart_1851924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851967 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 1, 3, 2]
def baseStart_1851967 : Nat := 118140960795 + 1851967 * 2 ^ 59
def prefixEnd_1851967 : Nat := 4983230072969 + 3 ^ 40 * 1851967 * 2
def baseEnd_1851967 : Nat := 950949227265260904295465

theorem tailTrace_1851967 : CollatzResearch.WordTrace tailWord_1851967 prefixEnd_1851967 950949227265260904295465 := by
  unfold tailWord_1851967
  simp only [CollatzResearch.WordTrace]
  refine ⟨67546785681647324627514155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45031190454431549751676103 67546785681647324627514155)
  ·
    refine ⟨101320178522470986941271233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67546785681647324627514155 101320178522470986941271233)
    ·
      refine ⟨75990133891853240205953425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101320178522470986941271233 75990133891853240205953425)
      ·
        refine ⟨56992600418889930154465069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75990133891853240205953425 56992600418889930154465069)
        ·
          refine ⟨21372225157083723807924401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56992600418889930154465069 21372225157083723807924401)
          ·
            refine ⟨16029168867812792855943301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21372225157083723807924401 16029168867812792855943301)
            ·
              refine ⟨3005469162714898660489369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16029168867812792855943301 3005469162714898660489369)
              ·
                refine ⟨2254101872036173995367027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005469162714898660489369 2254101872036173995367027)
                ·
                  refine ⟨3381152808054260993050541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254101872036173995367027 3381152808054260993050541)
                  ·
                    refine ⟨1267932303020347872393953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381152808054260993050541 1267932303020347872393953)
                    ·
                      refine ⟨950949227265260904295465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267932303020347872393953 950949227265260904295465)
                      ·
                        rfl

theorem cell23_1851967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_1851967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851967 prefixEnd_1851967 := by exact prefixLift 1851967
  have htrace : WordTrace (prefixWord ++ tailWord_1851967) baseStart_1851967 baseEnd_1851967 := by
    simpa [prefixWord, tailWord_1851967, baseEnd_1851967] using wordTrace_append hprefix tailTrace_1851967
  have hstable : (prefixWord ++ tailWord_1851967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851967).length < 2 ^ (prefixWord ++ tailWord_1851967).sum := by decide
  have hdescent : baseEnd_1851967 < baseStart_1851967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851974 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1851974 : Nat := 118140960795 + 1851974 * 2 ^ 59
def prefixEnd_1851974 : Nat := 4983230072969 + 3 ^ 40 * 1851974 * 2
def baseEnd_1851974 : Nat := 950952821629842376907933

theorem tailTrace_1851974 : CollatzResearch.WordTrace tailWord_1851974 prefixEnd_1851974 950952821629842376907933 := by
  unfold tailWord_1851974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110845031019436400719343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45031360661747976548679317 2110845031019436400719343)
  ·
    refine ⟨3166267546529154601079015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110845031019436400719343 3166267546529154601079015)
    ·
      refine ⟨4749401319793731901618523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166267546529154601079015 4749401319793731901618523)
      ·
        refine ⟨7124101979690597852427785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749401319793731901618523 7124101979690597852427785)
        ·
          refine ⟨5343076484767948389320839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7124101979690597852427785 5343076484767948389320839)
          ·
            refine ⟨8014614727151922583981259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343076484767948389320839 8014614727151922583981259)
            ·
              refine ⟨12021922090727883875971889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8014614727151922583981259 12021922090727883875971889)
              ·
                refine ⟨9016441568045912906978917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12021922090727883875971889 9016441568045912906978917)
                ·
                  refine ⟨1690582794008608670058547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9016441568045912906978917 1690582794008608670058547)
                  ·
                    refine ⟨2535874191012913005087821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690582794008608670058547 2535874191012913005087821)
                    ·
                      refine ⟨950952821629842376907933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2535874191012913005087821 950952821629842376907933)
                      ·
                        rfl

theorem cell23_1851974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1851974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851974 prefixEnd_1851974 := by exact prefixLift 1851974
  have htrace : WordTrace (prefixWord ++ tailWord_1851974) baseStart_1851974 baseEnd_1851974 := by
    simpa [prefixWord, tailWord_1851974, baseEnd_1851974] using wordTrace_append hprefix tailTrace_1851974
  have hstable : (prefixWord ++ tailWord_1851974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851974).length < 2 ^ (prefixWord ++ tailWord_1851974).sum := by decide
  have hdescent : baseEnd_1851974 < baseStart_1851974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851980 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 3, 4, 2]
def baseStart_1851980 : Nat := 118140960795 + 1851980 * 2 ^ 59
def prefixEnd_1851980 : Nat := 4983230072969 + 3 ^ 40 * 1851980 * 2
def baseEnd_1851980 : Nat := 950955902513769353432905

theorem tailTrace_1851980 : CollatzResearch.WordTrace tailWord_1851980 prefixEnd_1851980 950955902513769353432905 := by
  unfold tailWord_1851980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33773629915300113923868697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45031506553733485231824929 33773629915300113923868697)
  ·
    refine ⟨25330222436475085442901523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33773629915300113923868697 25330222436475085442901523)
    ·
      refine ⟨37995333654712628164352285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25330222436475085442901523 37995333654712628164352285)
      ·
        refine ⟨14248250120517235561632107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37995333654712628164352285 14248250120517235561632107)
        ·
          refine ⟨21372375180775853342448161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14248250120517235561632107 21372375180775853342448161)
          ·
            refine ⟨16029281385581890006836121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21372375180775853342448161 16029281385581890006836121)
            ·
              refine ⟨12021961039186417505127091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16029281385581890006836121 12021961039186417505127091)
              ·
                refine ⟨18032941558779626257690637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12021961039186417505127091 18032941558779626257690637)
                ·
                  refine ⟨6762353084542359846633989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18032941558779626257690637 6762353084542359846633989)
                  ·
                    refine ⟨1267941203351692471243873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6762353084542359846633989 1267941203351692471243873)
                    ·
                      refine ⟨950955902513769353432905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1267941203351692471243873 950955902513769353432905)
                      ·
                        rfl

theorem cell23_1851980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_1851980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1851980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1851980 prefixEnd_1851980 := by exact prefixLift 1851980
  have htrace : WordTrace (prefixWord ++ tailWord_1851980) baseStart_1851980 baseEnd_1851980 := by
    simpa [prefixWord, tailWord_1851980, baseEnd_1851980] using wordTrace_append hprefix tailTrace_1851980
  have hstable : (prefixWord ++ tailWord_1851980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851980).length < 2 ^ (prefixWord ++ tailWord_1851980).sum := by decide
  have hdescent : baseEnd_1851980 < baseStart_1851980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852008 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1852008 : Nat := 118140960795 + 1852008 * 2 ^ 59
def prefixEnd_1852008 : Nat := 4983230072969 + 3 ^ 40 * 1852008 * 2
def baseEnd_1852008 : Nat := 950970279972095243882777

theorem tailTrace_1852008 : CollatzResearch.WordTrace tailWord_1852008 prefixEnd_1852008 950970279972095243882777 := by
  unfold tailWord_1852008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33774140537249394314878339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45032187382999192419837785 33774140537249394314878339)
  ·
    refine ⟨50661210805874091472317509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33774140537249394314878339 50661210805874091472317509)
    ·
      refine ⟨9498977026101392151059533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50661210805874091472317509 9498977026101392151059533)
      ·
        refine ⟨3562116384788022056647325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9498977026101392151059533 3562116384788022056647325)
        ·
          refine ⟨1335793644295508271242747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3562116384788022056647325 1335793644295508271242747)
          ·
            refine ⟨2003690466443262406864121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335793644295508271242747 2003690466443262406864121)
            ·
              refine ⟨1502767849832446805148091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003690466443262406864121 1502767849832446805148091)
              ·
                refine ⟨2254151774748670207722137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502767849832446805148091 2254151774748670207722137)
                ·
                  refine ⟨1690613831061502655791603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254151774748670207722137 1690613831061502655791603)
                  ·
                    refine ⟨2535920746592253983687405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690613831061502655791603 2535920746592253983687405)
                    ·
                      refine ⟨950970279972095243882777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2535920746592253983687405 950970279972095243882777)
                      ·
                        rfl

theorem cell23_1852008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1852008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852008 prefixEnd_1852008 := by exact prefixLift 1852008
  have htrace : WordTrace (prefixWord ++ tailWord_1852008) baseStart_1852008 baseEnd_1852008 := by
    simpa [prefixWord, tailWord_1852008, baseEnd_1852008] using wordTrace_append hprefix tailTrace_1852008
  have hstable : (prefixWord ++ tailWord_1852008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852008).length < 2 ^ (prefixWord ++ tailWord_1852008).sum := by decide
  have hdescent : baseEnd_1852008 < baseStart_1852008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852053 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1852053 : Nat := 118140960795 + 1852053 * 2 ^ 59
def prefixEnd_1852053 : Nat := 4983230072969 + 3 ^ 40 * 1852053 * 2
def baseEnd_1852053 : Nat := 950993386601547567820069

theorem tailTrace_1852053 : CollatzResearch.WordTrace tailWord_1852053 prefixEnd_1852053 950993386601547567820069 := by
  unfold tailWord_1852053
  simp only [CollatzResearch.WordTrace]
  refine ⟨67549922359335761315144813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45033281572890507543429875 67549922359335761315144813)
  ·
    refine ⟨25331220884750910493179305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67549922359335761315144813 25331220884750910493179305)
    ·
      refine ⟨18998415663563182869884479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25331220884750910493179305 18998415663563182869884479)
      ·
        refine ⟨28497623495344774304826719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18998415663563182869884479 28497623495344774304826719)
        ·
          refine ⟨42746435243017161457240079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28497623495344774304826719 42746435243017161457240079)
          ·
            refine ⟨64119652864525742185860119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42746435243017161457240079 64119652864525742185860119)
            ·
              refine ⟨96179479296788613278790179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64119652864525742185860119 96179479296788613278790179)
              ·
                refine ⟨144269218945182919918185269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96179479296788613278790179 144269218945182919918185269)
                ·
                  refine ⟨13525239276110898742329869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144269218945182919918185269 13525239276110898742329869)
                  ·
                    refine ⟨5071964728541587028373701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13525239276110898742329869 5071964728541587028373701)
                    ·
                      refine ⟨950993386601547567820069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5071964728541587028373701 950993386601547567820069)
                      ·
                        rfl

theorem cell23_1852053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1852053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852053 prefixEnd_1852053 := by exact prefixLift 1852053
  have htrace : WordTrace (prefixWord ++ tailWord_1852053) baseStart_1852053 baseEnd_1852053 := by
    simpa [prefixWord, tailWord_1852053, baseEnd_1852053] using wordTrace_append hprefix tailTrace_1852053
  have hstable : (prefixWord ++ tailWord_1852053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852053).length < 2 ^ (prefixWord ++ tailWord_1852053).sum := by decide
  have hdescent : baseEnd_1852053 < baseStart_1852053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852060 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1852060 : Nat := 118140960795 + 1852060 * 2 ^ 59
def prefixEnd_1852060 : Nat := 4983230072969 + 3 ^ 40 * 1852060 * 2
def baseEnd_1852060 : Nat := 950996980966129040432537

theorem tailTrace_1852060 : CollatzResearch.WordTrace tailWord_1852060 prefixEnd_1852060 950996980966129040432537 := by
  unfold tailWord_1852060
  simp only [CollatzResearch.WordTrace]
  refine ⟨33775088835155200755324817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45033451780206934340433089 33775088835155200755324817)
  ·
    refine ⟨25331316626366400566493613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33775088835155200755324817 25331316626366400566493613)
    ·
      refine ⟨9499243734887400212435105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25331316626366400566493613 9499243734887400212435105)
      ·
        refine ⟨7124432801165550159326329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9499243734887400212435105 7124432801165550159326329)
        ·
          refine ⟨5343324600874162619494747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7124432801165550159326329 5343324600874162619494747)
          ·
            refine ⟨8014986901311243929242121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343324600874162619494747 8014986901311243929242121)
            ·
              refine ⟨6011240175983432946931591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014986901311243929242121 6011240175983432946931591)
              ·
                refine ⟨9016860263975149420397387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011240175983432946931591 9016860263975149420397387)
                ·
                  refine ⟨13525290395962724130596081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9016860263975149420397387 13525290395962724130596081)
                  ·
                    refine ⟨10143967796972043097947061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13525290395962724130596081 10143967796972043097947061)
                    ·
                      refine ⟨950996980966129040432537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10143967796972043097947061 950996980966129040432537)
                      ·
                        rfl

theorem cell23_1852060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1852060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852060 prefixEnd_1852060 := by exact prefixLift 1852060
  have htrace : WordTrace (prefixWord ++ tailWord_1852060) baseStart_1852060 baseEnd_1852060 := by
    simpa [prefixWord, tailWord_1852060, baseEnd_1852060] using wordTrace_append hprefix tailTrace_1852060
  have hstable : (prefixWord ++ tailWord_1852060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852060).length < 2 ^ (prefixWord ++ tailWord_1852060).sum := by decide
  have hdescent : baseEnd_1852060 < baseStart_1852060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852090 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_1852090 : Nat := 118140960795 + 1852090 * 2 ^ 59
def prefixEnd_1852090 : Nat := 4983230072969 + 3 ^ 40 * 1852090 * 2
def baseEnd_1852090 : Nat := 951012385385763923057399

theorem tailTrace_1852090 : CollatzResearch.WordTrace tailWord_1852090 prefixEnd_1852090 951012385385763923057399 := by
  unfold tailWord_1852090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16887817965050429158560431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45034181240134477756161149 16887817965050429158560431)
  ·
    refine ⟨25331726947575643737840647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16887817965050429158560431 25331726947575643737840647)
    ·
      refine ⟨37997590421363465606760971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25331726947575643737840647 37997590421363465606760971)
      ·
        refine ⟨56996385632045198410141457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37997590421363465606760971 56996385632045198410141457)
        ·
          refine ⟨42747289224033898807606093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56996385632045198410141457 42747289224033898807606093)
          ·
            refine ⟨16030233459012712052852285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42747289224033898807606093 16030233459012712052852285)
            ·
              refine ⟨6011337547129767019819607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16030233459012712052852285 6011337547129767019819607)
              ·
                refine ⟨9017006320694650529729411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011337547129767019819607 9017006320694650529729411)
                ·
                  refine ⟨13525509481041975794594117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9017006320694650529729411 13525509481041975794594117)
                  ·
                    refine ⟨2536033027695370461486397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13525509481041975794594117 2536033027695370461486397)
                    ·
                      refine ⟨951012385385763923057399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2536033027695370461486397 951012385385763923057399)
                      ·
                        rfl

theorem cell23_1852090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_1852090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852090 prefixEnd_1852090 := by exact prefixLift 1852090
  have htrace : WordTrace (prefixWord ++ tailWord_1852090) baseStart_1852090 baseEnd_1852090 := by
    simpa [prefixWord, tailWord_1852090, baseEnd_1852090] using wordTrace_append hprefix tailTrace_1852090
  have hstable : (prefixWord ++ tailWord_1852090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852090).length < 2 ^ (prefixWord ++ tailWord_1852090).sum := by decide
  have hdescent : baseEnd_1852090 < baseStart_1852090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852100 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1852100 : Nat := 118140960795 + 1852100 * 2 ^ 59
def prefixEnd_1852100 : Nat := 4983230072969 + 3 ^ 40 * 1852100 * 2
def baseEnd_1852100 : Nat := 951017520192308883932353

theorem tailTrace_1852100 : CollatzResearch.WordTrace tailWord_1852100 prefixEnd_1852100 951017520192308883932353 := by
  unfold tailWord_1852100
  simp only [CollatzResearch.WordTrace]
  refine ⟨33775818295082744171052877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45034424393443658894737169 33775818295082744171052877)
  ·
    refine ⟨12665931860656029064144829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33775818295082744171052877 12665931860656029064144829)
    ·
      refine ⟨4749724447746010899054311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12665931860656029064144829 4749724447746010899054311)
      ·
        refine ⟨7124586671619016348581467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749724447746010899054311 7124586671619016348581467)
        ·
          refine ⟨10686880007428524522872201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124586671619016348581467 10686880007428524522872201)
          ·
            refine ⟨8015160005571393392154151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10686880007428524522872201 8015160005571393392154151)
            ·
              refine ⟨12022740008357090088231227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8015160005571393392154151 12022740008357090088231227)
              ·
                refine ⟨18034110012535635132346841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12022740008357090088231227 18034110012535635132346841)
                ·
                  refine ⟨13525582509401726349260131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18034110012535635132346841 13525582509401726349260131)
                  ·
                    refine ⟨20288373764102589523890197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13525582509401726349260131 20288373764102589523890197)
                    ·
                      refine ⟨951017520192308883932353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20288373764102589523890197 951017520192308883932353)
                      ·
                        rfl

theorem cell23_1852100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1852100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852100 prefixEnd_1852100 := by exact prefixLift 1852100
  have htrace : WordTrace (prefixWord ++ tailWord_1852100) baseStart_1852100 baseEnd_1852100 := by
    simpa [prefixWord, tailWord_1852100, baseEnd_1852100] using wordTrace_append hprefix tailTrace_1852100
  have hstable : (prefixWord ++ tailWord_1852100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852100).length < 2 ^ (prefixWord ++ tailWord_1852100).sum := by decide
  have hdescent : baseEnd_1852100 < baseStart_1852100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852110 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_1852110 : Nat := 118140960795 + 1852110 * 2 ^ 59
def prefixEnd_1852110 : Nat := 4983230072969 + 3 ^ 40 * 1852110 * 2
def baseEnd_1852110 : Nat := 105669183888761538311923

theorem tailTrace_1852110 : CollatzResearch.WordTrace tailWord_1852110 prefixEnd_1852110 105669183888761538311923 := by
  unfold tailWord_1852110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444000165016157506246223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45034667546752840033313189 8444000165016157506246223)
  ·
    refine ⟨12666000247524236259369335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8444000165016157506246223 12666000247524236259369335)
    ·
      refine ⟨18999000371286354389054003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12666000247524236259369335 18999000371286354389054003)
      ·
        refine ⟨28498500556929531583581005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18999000371286354389054003 28498500556929531583581005)
        ·
          refine ⟨10686937708848574343842877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28498500556929531583581005 10686937708848574343842877)
          ·
            refine ⟨4007601640818215378941079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10686937708848574343842877 4007601640818215378941079)
            ·
              refine ⟨6011402461227323068411619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007601640818215378941079 6011402461227323068411619)
              ·
                refine ⟨9017103691840984602617429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011402461227323068411619 9017103691840984602617429)
                ·
                  refine ⟨105669183888761538311923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9017103691840984602617429 105669183888761538311923)
                  ·
                    rfl

theorem cell23_1852110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_1852110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852110 prefixEnd_1852110 := by exact prefixLift 1852110
  have htrace : WordTrace (prefixWord ++ tailWord_1852110) baseStart_1852110 baseEnd_1852110 := by
    simpa [prefixWord, tailWord_1852110, baseEnd_1852110] using wordTrace_append hprefix tailTrace_1852110
  have hstable : (prefixWord ++ tailWord_1852110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852110).length < 2 ^ (prefixWord ++ tailWord_1852110).sum := by decide
  have hdescent : baseEnd_1852110 < baseStart_1852110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852113 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1852113 : Nat := 118140960795 + 1852113 * 2 ^ 59
def prefixEnd_1852113 : Nat := 4983230072969 + 3 ^ 40 * 1852113 * 2
def baseEnd_1852113 : Nat := 951024195440817333069793

theorem tailTrace_1852113 : CollatzResearch.WordTrace tailWord_1852113 prefixEnd_1852113 951024195440817333069793 := by
  unfold tailWord_1852113
  simp only [CollatzResearch.WordTrace]
  refine ⟨67552110739118391562328993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45034740492745594374885995 67552110739118391562328993)
  ·
    refine ⟨50664083054338793671746745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67552110739118391562328993 50664083054338793671746745)
    ·
      refine ⟨37998062290754095253810059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50664083054338793671746745 37998062290754095253810059)
      ·
        refine ⟨56997093436131142880715089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37998062290754095253810059 56997093436131142880715089)
        ·
          refine ⟨42747820077098357160536317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56997093436131142880715089 42747820077098357160536317)
          ·
            refine ⟨16030432528911883935201119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42747820077098357160536317 16030432528911883935201119)
            ·
              refine ⟨24045648793367825902801679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16030432528911883935201119 24045648793367825902801679)
              ·
                refine ⟨36068473190051738854202519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24045648793367825902801679 36068473190051738854202519)
                ·
                  refine ⟨54102709785077608281303779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36068473190051738854202519 54102709785077608281303779)
                  ·
                    refine ⟨81154064677616412421955669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54102709785077608281303779 81154064677616412421955669)
                    ·
                      refine ⟨951024195440817333069793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 81154064677616412421955669 951024195440817333069793)
                      ·
                        rfl

theorem cell23_1852113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1852113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852113 prefixEnd_1852113 := by exact prefixLift 1852113
  have htrace : WordTrace (prefixWord ++ tailWord_1852113) baseStart_1852113 baseEnd_1852113 := by
    simpa [prefixWord, tailWord_1852113, baseEnd_1852113] using wordTrace_append hprefix tailTrace_1852113
  have hstable : (prefixWord ++ tailWord_1852113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852113).length < 2 ^ (prefixWord ++ tailWord_1852113).sum := by decide
  have hdescent : baseEnd_1852113 < baseStart_1852113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852114 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1852114 : Nat := 118140960795 + 1852114 * 2 ^ 59
def prefixEnd_1852114 : Nat := 4983230072969 + 3 ^ 40 * 1852114 * 2
def baseEnd_1852114 : Nat := 317008236307157276385763

theorem tailTrace_1852114 : CollatzResearch.WordTrace tailWord_1852114 prefixEnd_1852114 317008236307157276385763 := by
  unfold tailWord_1852114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888036803028692183278849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45034764808076512488743597 16888036803028692183278849)
  ·
    refine ⟨12666027602271519137459137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16888036803028692183278849 12666027602271519137459137)
    ·
      refine ⟨9499520701703639353094353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12666027602271519137459137 9499520701703639353094353)
      ·
        refine ⟨7124640526277729514820765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9499520701703639353094353 7124640526277729514820765)
        ·
          refine ⟨2671740197354148568057787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7124640526277729514820765 2671740197354148568057787)
          ·
            refine ⟨4007610296031222852086681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671740197354148568057787 4007610296031222852086681)
            ·
              refine ⟨3005707722023417139065011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4007610296031222852086681 3005707722023417139065011)
              ·
                refine ⟨4508561583035125708597517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005707722023417139065011 4508561583035125708597517)
                ·
                  refine ⟨1690710593638172140724069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4508561583035125708597517 1690710593638172140724069)
                  ·
                    refine ⟨317008236307157276385763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690710593638172140724069 317008236307157276385763)
                    ·
                      rfl

theorem cell23_1852114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1852114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852114 prefixEnd_1852114 := by exact prefixLift 1852114
  have htrace : WordTrace (prefixWord ++ tailWord_1852114) baseStart_1852114 baseEnd_1852114 := by
    simpa [prefixWord, tailWord_1852114, baseEnd_1852114] using wordTrace_append hprefix tailTrace_1852114
  have hstable : (prefixWord ++ tailWord_1852114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852114).length < 2 ^ (prefixWord ++ tailWord_1852114).sum := by decide
  have hdescent : baseEnd_1852114 < baseStart_1852114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852127 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 6]
def baseStart_1852127 : Nat := 118140960795 + 1852127 * 2 ^ 59
def prefixEnd_1852127 : Nat := 4983230072969 + 3 ^ 40 * 1852127 * 2
def baseEnd_1852127 : Nat := 105670153796664475366081

theorem tailTrace_1852127 : CollatzResearch.WordTrace tailWord_1852127 prefixEnd_1852127 105670153796664475366081 := by
  unfold tailWord_1852127
  simp only [CollatzResearch.WordTrace]
  refine ⟨67552621361067671953338635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45035080907378447968892423 67552621361067671953338635)
  ·
    refine ⟨101328932041601507930007953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67552621361067671953338635 101328932041601507930007953)
    ·
      refine ⟨75996699031201130947505965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101328932041601507930007953 75996699031201130947505965)
      ·
        refine ⟨28498762136700424105314737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75996699031201130947505965 28498762136700424105314737)
        ·
          refine ⟨21374071602525318078986053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28498762136700424105314737 21374071602525318078986053)
          ·
            refine ⟨4007638425473497139809885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21374071602525318078986053 4007638425473497139809885)
            ·
              refine ⟨1502864409552561427428707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4007638425473497139809885 1502864409552561427428707)
              ·
                refine ⟨2254296614328842141143061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502864409552561427428707 2254296614328842141143061)
                ·
                  refine ⟨105670153796664475366081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2254296614328842141143061 105670153796664475366081)
                  ·
                    rfl

theorem cell23_1852127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 6].length) (baseStart_1852127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852127 prefixEnd_1852127 := by exact prefixLift 1852127
  have htrace : WordTrace (prefixWord ++ tailWord_1852127) baseStart_1852127 baseEnd_1852127 := by
    simpa [prefixWord, tailWord_1852127, baseEnd_1852127] using wordTrace_append hprefix tailTrace_1852127
  have hstable : (prefixWord ++ tailWord_1852127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852127).length < 2 ^ (prefixWord ++ tailWord_1852127).sum := by decide
  have hdescent : baseEnd_1852127 < baseStart_1852127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852137 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 3]
def baseStart_1852137 : Nat := 118140960795 + 1852137 * 2 ^ 59
def prefixEnd_1852137 : Nat := 4983230072969 + 3 ^ 40 * 1852137 * 2
def baseEnd_1852137 : Nat := 951036518976525239169683

theorem tailTrace_1852137 : CollatzResearch.WordTrace tailWord_1852137 prefixEnd_1852137 951036518976525239169683 := by
  unfold tailWord_1852137
  simp only [CollatzResearch.WordTrace]
  refine ⟨67552986091031443661202665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45035324060687629107468443 67552986091031443661202665)
  ·
    refine ⟨50664739568273582745901999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67552986091031443661202665 50664739568273582745901999)
    ·
      refine ⟨75997109352410374118852999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50664739568273582745901999 75997109352410374118852999)
      ·
        refine ⟨113995664028615561178279499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75997109352410374118852999 113995664028615561178279499)
        ·
          refine ⟨170993496042923341767419249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113995664028615561178279499 170993496042923341767419249)
          ·
            refine ⟨128245122032192506325564437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170993496042923341767419249 128245122032192506325564437)
            ·
              refine ⟨6011490095259023734010833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128245122032192506325564437 6011490095259023734010833)
              ·
                refine ⟨4508617571444267800508125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6011490095259023734010833 4508617571444267800508125)
                ·
                  refine ⟨1690731589291600425190547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4508617571444267800508125 1690731589291600425190547)
                  ·
                    refine ⟨2536097383937400637785821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690731589291600425190547 2536097383937400637785821)
                    ·
                      refine ⟨951036518976525239169683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2536097383937400637785821 951036518976525239169683)
                      ·
                        rfl

theorem cell23_1852137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 1, 3].length) (baseStart_1852137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852137 prefixEnd_1852137 := by exact prefixLift 1852137
  have htrace : WordTrace (prefixWord ++ tailWord_1852137) baseStart_1852137 baseEnd_1852137 := by
    simpa [prefixWord, tailWord_1852137, baseEnd_1852137] using wordTrace_append hprefix tailTrace_1852137
  have hstable : (prefixWord ++ tailWord_1852137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852137).length < 2 ^ (prefixWord ++ tailWord_1852137).sum := by decide
  have hdescent : baseEnd_1852137 < baseStart_1852137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852147 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 2, 3, 2]
def baseStart_1852147 : Nat := 118140960795 + 1852147 * 2 ^ 59
def prefixEnd_1852147 : Nat := 4983230072969 + 3 ^ 40 * 1852147 * 2
def baseEnd_1852147 : Nat := 951041653783070200044637

theorem tailTrace_1852147 : CollatzResearch.WordTrace tailWord_1852147 prefixEnd_1852147 951041653783070200044637 := by
  unfold tailWord_1852147
  simp only [CollatzResearch.WordTrace]
  refine ⟨67553350820995215369066695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45035567213996810246044463 67553350820995215369066695)
  ·
    refine ⟨101330026231492823053600043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67553350820995215369066695 101330026231492823053600043)
    ·
      refine ⟨151995039347239234580400065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101330026231492823053600043 151995039347239234580400065)
      ·
        refine ⟨113996279510429425935300049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151995039347239234580400065 113996279510429425935300049)
        ·
          refine ⟨85497209632822069451475037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113996279510429425935300049 85497209632822069451475037)
          ·
            refine ⟨32061453612308276044303139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85497209632822069451475037 32061453612308276044303139)
            ·
              refine ⟨48092180418462414066454709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32061453612308276044303139 48092180418462414066454709)
              ·
                refine ⟨4508641914230851318730129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48092180418462414066454709 4508641914230851318730129)
                ·
                  refine ⟨3381481435673138489047597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508641914230851318730129 3381481435673138489047597)
                  ·
                    refine ⟨1268055538377426933392849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381481435673138489047597 1268055538377426933392849)
                    ·
                      refine ⟨951041653783070200044637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268055538377426933392849 951041653783070200044637)
                      ·
                        rfl

theorem cell23_1852147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3, 2].length) (baseStart_1852147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852147 prefixEnd_1852147 := by exact prefixLift 1852147
  have htrace : WordTrace (prefixWord ++ tailWord_1852147) baseStart_1852147 baseEnd_1852147 := by
    simpa [prefixWord, tailWord_1852147, baseEnd_1852147] using wordTrace_append hprefix tailTrace_1852147
  have hstable : (prefixWord ++ tailWord_1852147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852147).length < 2 ^ (prefixWord ++ tailWord_1852147).sum := by decide
  have hdescent : baseEnd_1852147 < baseStart_1852147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852164 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1852164 : Nat := 118140960795 + 1852164 * 2 ^ 59
def prefixEnd_1852164 : Nat := 4983230072969 + 3 ^ 40 * 1852164 * 2
def baseEnd_1852164 : Nat := 951050382954196633532059

theorem tailTrace_1852164 : CollatzResearch.WordTrace tailWord_1852164 prefixEnd_1852164 951050382954196633532059 := by
  unfold tailWord_1852164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33776985430966813636217773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45035980574622418181623697 33776985430966813636217773)
  ·
    refine ⟨12666369536612555113581665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33776985430966813636217773 12666369536612555113581665)
    ·
      refine ⟨9499777152459416335186249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12666369536612555113581665 9499777152459416335186249)
      ·
        refine ⟨7124832864344562251389687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9499777152459416335186249 7124832864344562251389687)
        ·
          refine ⟨10687249296516843377084531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124832864344562251389687 10687249296516843377084531)
          ·
            refine ⟨16030873944775265065626797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10687249296516843377084531 16030873944775265065626797)
            ·
              refine ⟨6011577729290724399610049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16030873944775265065626797 6011577729290724399610049)
              ·
                refine ⟨4508683296968043299707537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6011577729290724399610049 4508683296968043299707537)
                ·
                  refine ⟨3381512472726032474780653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4508683296968043299707537 3381512472726032474780653)
                  ·
                    refine ⟨1268067177272262178042745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3381512472726032474780653 1268067177272262178042745)
                    ·
                      refine ⟨951050382954196633532059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268067177272262178042745 951050382954196633532059)
                      ·
                        rfl

theorem cell23_1852164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1852164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852164 prefixEnd_1852164 := by exact prefixLift 1852164
  have htrace : WordTrace (prefixWord ++ tailWord_1852164) baseStart_1852164 baseEnd_1852164 := by
    simpa [prefixWord, tailWord_1852164, baseEnd_1852164] using wordTrace_append hprefix tailTrace_1852164
  have hstable : (prefixWord ++ tailWord_1852164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852164).length < 2 ^ (prefixWord ++ tailWord_1852164).sum := by decide
  have hdescent : baseEnd_1852164 < baseStart_1852164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852178 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 6]
def baseStart_1852178 : Nat := 118140960795 + 1852178 * 2 ^ 59
def prefixEnd_1852178 : Nat := 4983230072969 + 3 ^ 40 * 1852178 * 2
def baseEnd_1852178 : Nat := 105673063520373286528555

theorem tailTrace_1852178 : CollatzResearch.WordTrace tailWord_1852178 prefixEnd_1852178 105673063520373286528555 := by
  unfold tailWord_1852178
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888620370970726915861297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45036320989255271775630125 16888620370970726915861297)
  ·
    refine ⟨12666465278228045186895973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16888620370970726915861297 12666465278228045186895973)
    ·
      refine ⟨2374962239667758472542995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12666465278228045186895973 2374962239667758472542995)
      ·
        refine ⟨3562443359501637708814493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374962239667758472542995 3562443359501637708814493)
        ·
          refine ⟨1335916259813114140805435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3562443359501637708814493 1335916259813114140805435)
          ·
            refine ⟨2003874389719671211208153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335916259813114140805435 2003874389719671211208153)
            ·
              refine ⟨1502905792289753408406115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003874389719671211208153 1502905792289753408406115)
              ·
                refine ⟨2254358688434630112609173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502905792289753408406115 2254358688434630112609173)
                ·
                  refine ⟨105673063520373286528555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2254358688434630112609173 105673063520373286528555)
                  ·
                    rfl

theorem cell23_1852178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_1852178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852178 prefixEnd_1852178 := by exact prefixLift 1852178
  have htrace : WordTrace (prefixWord ++ tailWord_1852178) baseStart_1852178 baseEnd_1852178 := by
    simpa [prefixWord, tailWord_1852178, baseEnd_1852178] using wordTrace_append hprefix tailTrace_1852178
  have hstable : (prefixWord ++ tailWord_1852178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852178).length < 2 ^ (prefixWord ++ tailWord_1852178).sum := by decide
  have hdescent : baseEnd_1852178 < baseStart_1852178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852194 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_1852194 : Nat := 118140960795 + 1852194 * 2 ^ 59
def prefixEnd_1852194 : Nat := 4983230072969 + 3 ^ 40 * 1852194 * 2
def baseEnd_1852194 : Nat := 951065787373831516156921

theorem tailTrace_1852194 : CollatzResearch.WordTrace tailWord_1852194 prefixEnd_1852194 951065787373831516156921 := by
  unfold tailWord_1852194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888766262956235599006909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45036710034549961597351757 16888766262956235599006909)
  ·
    refine ⟨6333287348608588349627591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16888766262956235599006909 6333287348608588349627591)
    ·
      refine ⟨9499931022912882524441387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6333287348608588349627591 9499931022912882524441387)
      ·
        refine ⟨14249896534369323786662081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9499931022912882524441387 14249896534369323786662081)
        ·
          refine ⟨10687422400776992839996561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14249896534369323786662081 10687422400776992839996561)
          ·
            refine ⟨8015566800582744629997421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10687422400776992839996561 8015566800582744629997421)
            ·
              refine ⟨3005837550218529236249033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8015566800582744629997421 3005837550218529236249033)
              ·
                refine ⟨2254378162663896927186775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005837550218529236249033 2254378162663896927186775)
                ·
                  refine ⟨3381567243995845390780163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254378162663896927186775 3381567243995845390780163)
                  ·
                    refine ⟨5072350865993768086170245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3381567243995845390780163 5072350865993768086170245)
                    ·
                      refine ⟨951065787373831516156921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5072350865993768086170245 951065787373831516156921)
                      ·
                        rfl

theorem cell23_1852194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_1852194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852194 prefixEnd_1852194 := by exact prefixLift 1852194
  have htrace : WordTrace (prefixWord ++ tailWord_1852194) baseStart_1852194 baseEnd_1852194 := by
    simpa [prefixWord, tailWord_1852194, baseEnd_1852194] using wordTrace_append hprefix tailTrace_1852194
  have hstable : (prefixWord ++ tailWord_1852194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852194).length < 2 ^ (prefixWord ++ tailWord_1852194).sum := by decide
  have hdescent : baseEnd_1852194 < baseStart_1852194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852197 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_1852197 : Nat := 118140960795 + 1852197 * 2 ^ 59
def prefixEnd_1852197 : Nat := 4983230072969 + 3 ^ 40 * 1852197 * 2
def baseEnd_1852197 : Nat := 951067327815795004419407

theorem tailTrace_1852197 : CollatzResearch.WordTrace tailWord_1852197 prefixEnd_1852197 951067327815795004419407 := by
  unfold tailWord_1852197
  simp only [CollatzResearch.WordTrace]
  refine ⟨67555174470814073908386845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45036782980542715938924563 67555174470814073908386845)
  ·
    refine ⟨25333190426555277715645067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67555174470814073908386845 25333190426555277715645067)
    ·
      refine ⟨37999785639832916573467601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25333190426555277715645067 37999785639832916573467601)
      ·
        refine ⟨28499839229874687430100701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37999785639832916573467601 28499839229874687430100701)
        ·
          refine ⟨10687439711203007786287763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28499839229874687430100701 10687439711203007786287763)
          ·
            refine ⟨16031159566804511679431645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10687439711203007786287763 16031159566804511679431645)
            ·
              refine ⟨6011684837551691879786867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16031159566804511679431645 6011684837551691879786867)
              ·
                refine ⟨9017527256327537819680301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6011684837551691879786867 9017527256327537819680301)
                ·
                  refine ⟨3381572721122826682380113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9017527256327537819680301 3381572721122826682380113)
                  ·
                    refine ⟨2536179540842120011785085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3381572721122826682380113 2536179540842120011785085)
                    ·
                      refine ⟨951067327815795004419407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2536179540842120011785085 951067327815795004419407)
                      ·
                        rfl

theorem cell23_1852197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_1852197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852197 prefixEnd_1852197 := by exact prefixLift 1852197
  have htrace : WordTrace (prefixWord ++ tailWord_1852197) baseStart_1852197 baseEnd_1852197 := by
    simpa [prefixWord, tailWord_1852197, baseEnd_1852197] using wordTrace_append hprefix tailTrace_1852197
  have hstable : (prefixWord ++ tailWord_1852197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852197).length < 2 ^ (prefixWord ++ tailWord_1852197).sum := by decide
  have hdescent : baseEnd_1852197 < baseStart_1852197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852200 : List Nat := [2, 1, 5, 1, 1, 1, 1, 11]
def baseStart_1852200 : Nat := 118140960795 + 1852200 * 2 ^ 59
def prefixEnd_1852200 : Nat := 4983230072969 + 3 ^ 40 * 1852200 * 2
def baseEnd_1852200 : Nat := 35224772898435499728959

theorem tailTrace_1852200 : CollatzResearch.WordTrace tailWord_1852200 prefixEnd_1852200 35224772898435499728959 := by
  unfold tailWord_1852200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33777641944901602710373027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45036855926535470280497369 33777641944901602710373027)
  ·
    refine ⟨50666462917352404065559541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33777641944901602710373027 50666462917352404065559541)
    ·
      refine ⟨4749980898501787881146207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50666462917352404065559541 4749980898501787881146207)
      ·
        refine ⟨7124971347752681821719311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749980898501787881146207 7124971347752681821719311)
        ·
          refine ⟨10687457021629022732578967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124971347752681821719311 10687457021629022732578967)
          ·
            refine ⟨16031185532443534098868451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10687457021629022732578967 16031185532443534098868451)
            ·
              refine ⟨24046778298665301148302677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16031185532443534098868451 24046778298665301148302677)
              ·
                refine ⟨35224772898435499728959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24046778298665301148302677 35224772898435499728959)
                ·
                  rfl

theorem cell23_1852200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 11].length) (baseStart_1852200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852200 prefixEnd_1852200 := by exact prefixLift 1852200
  have htrace : WordTrace (prefixWord ++ tailWord_1852200) baseStart_1852200 baseEnd_1852200 := by
    simpa [prefixWord, tailWord_1852200, baseEnd_1852200] using wordTrace_append hprefix tailTrace_1852200
  have hstable : (prefixWord ++ tailWord_1852200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852200).length < 2 ^ (prefixWord ++ tailWord_1852200).sum := by decide
  have hdescent : baseEnd_1852200 < baseStart_1852200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852221 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_1852221 : Nat := 118140960795 + 1852221 * 2 ^ 59
def prefixEnd_1852221 : Nat := 4983230072969 + 3 ^ 40 * 1852221 * 2
def baseEnd_1852221 : Nat := 317026550450500970173099

theorem tailTrace_1852221 : CollatzResearch.WordTrace tailWord_1852221 prefixEnd_1852221 317026550450500970173099 := by
  unfold tailWord_1852221
  simp only [CollatzResearch.WordTrace]
  refine ⟨67556049822727126007260517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45037366548484750671507011 67556049822727126007260517)
  ·
    refine ⟨12666759341761336126361347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67556049822727126007260517 12666759341761336126361347)
    ·
      refine ⟨19000139012642004189542021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12666759341761336126361347 19000139012642004189542021)
      ·
        refine ⟨3562526064870375785539129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19000139012642004189542021 3562526064870375785539129)
        ·
          refine ⟨2671894548652781839154347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3562526064870375785539129 2671894548652781839154347)
          ·
            refine ⟨4007841822979172758731521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671894548652781839154347 4007841822979172758731521)
            ·
              refine ⟨3005881367234379569048641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4007841822979172758731521 3005881367234379569048641)
              ·
                refine ⟨2254411025425784676786481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005881367234379569048641 2254411025425784676786481)
                ·
                  refine ⟨1690808269069338507589861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254411025425784676786481 1690808269069338507589861)
                  ·
                    refine ⟨317026550450500970173099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1690808269069338507589861 317026550450500970173099)
                    ·
                      rfl

theorem cell23_1852221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_1852221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852221 prefixEnd_1852221 := by exact prefixLift 1852221
  have htrace : WordTrace (prefixWord ++ tailWord_1852221) baseStart_1852221 baseEnd_1852221 := by
    simpa [prefixWord, tailWord_1852221, baseEnd_1852221] using wordTrace_append hprefix tailTrace_1852221
  have hstable : (prefixWord ++ tailWord_1852221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852221).length < 2 ^ (prefixWord ++ tailWord_1852221).sum := by decide
  have hdescent : baseEnd_1852221 < baseStart_1852221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852222 : List Nat := [4, 2, 1, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_1852222 : Nat := 118140960795 + 1852222 * 2 ^ 59
def prefixEnd_1852222 : Nat := 4983230072969 + 3 ^ 40 * 1852222 * 2
def baseEnd_1852222 : Nat := 951080164832157406606793

theorem tailTrace_1852222 : CollatzResearch.WordTrace tailWord_1852222 prefixEnd_1852222 951080164832157406606793 := by
  unfold tailWord_1852222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444510786965437897255865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45037390863815668785364613 8444510786965437897255865)
  ·
    refine ⟨6333383090224078422941899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8444510786965437897255865 6333383090224078422941899)
    ·
      refine ⟨9500074635336117634412849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6333383090224078422941899 9500074635336117634412849)
      ·
        refine ⟨7125055976502088225809637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9500074635336117634412849 7125055976502088225809637)
        ·
          refine ⟨1335947995594141542339307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7125055976502088225809637 1335947995594141542339307)
          ·
            refine ⟨2003921993391212313508961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335947995594141542339307 2003921993391212313508961)
            ·
              refine ⟨1502941495043409235131721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003921993391212313508961 1502941495043409235131721)
              ·
                refine ⟨1127206121282556926348791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502941495043409235131721 1127206121282556926348791)
                ·
                  refine ⟨1690809181923835389523187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127206121282556926348791 1690809181923835389523187)
                  ·
                    refine ⟨2536213772885753084284781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690809181923835389523187 2536213772885753084284781)
                    ·
                      refine ⟨951080164832157406606793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2536213772885753084284781 951080164832157406606793)
                      ·
                        rfl

theorem cell23_1852222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_1852222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852222 prefixEnd_1852222 := by exact prefixLift 1852222
  have htrace : WordTrace (prefixWord ++ tailWord_1852222) baseStart_1852222 baseEnd_1852222 := by
    simpa [prefixWord, tailWord_1852222, baseEnd_1852222] using wordTrace_append hprefix tailTrace_1852222
  have hstable : (prefixWord ++ tailWord_1852222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852222).length < 2 ^ (prefixWord ++ tailWord_1852222).sum := by decide
  have hdescent : baseEnd_1852222 < baseStart_1852222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852277 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1852277 : Nat := 118140960795 + 1852277 * 2 ^ 59
def prefixEnd_1852277 : Nat := 4983230072969 + 3 ^ 40 * 1852277 * 2
def baseEnd_1852277 : Nat := 317036135422718230473013

theorem tailTrace_1852277 : CollatzResearch.WordTrace tailWord_1852277 prefixEnd_1852277 317036135422718230473013 := by
  unfold tailWord_1852277
  simp only [CollatzResearch.WordTrace]
  refine ⟨67558092310524247571299085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45038728207016165047532723 67558092310524247571299085)
  ·
    refine ⟨25334284616446592839237157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67558092310524247571299085 25334284616446592839237157)
    ·
      refine ⟨4750178365583736157356967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25334284616446592839237157 4750178365583736157356967)
      ·
        refine ⟨7125267548375604236035451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750178365583736157356967 7125267548375604236035451)
        ·
          refine ⟨10687901322563406354053177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7125267548375604236035451 10687901322563406354053177)
          ·
            refine ⟨8015925991922554765539883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10687901322563406354053177 8015925991922554765539883)
            ·
              refine ⟨12023888987883832148309825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8015925991922554765539883 12023888987883832148309825)
              ·
                refine ⟨9017916740912874111232369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12023888987883832148309825 9017916740912874111232369)
                ·
                  refine ⟨6763437555684655583424277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9017916740912874111232369 6763437555684655583424277)
                  ·
                    refine ⟨317036135422718230473013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6763437555684655583424277 317036135422718230473013)
                    ·
                      rfl

theorem cell23_1852277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1852277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852277 prefixEnd_1852277 := by exact prefixLift 1852277
  have htrace : WordTrace (prefixWord ++ tailWord_1852277) baseStart_1852277 baseEnd_1852277 := by
    simpa [prefixWord, tailWord_1852277, baseEnd_1852277] using wordTrace_append hprefix tailTrace_1852277
  have hstable : (prefixWord ++ tailWord_1852277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852277).length < 2 ^ (prefixWord ++ tailWord_1852277).sum := by decide
  have hdescent : baseEnd_1852277 < baseStart_1852277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852278 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1852278 : Nat := 118140960795 + 1852278 * 2 ^ 59
def prefixEnd_1852278 : Nat := 4983230072969 + 3 ^ 40 * 1852278 * 2
def baseEnd_1852278 : Nat := 951108919748809187506535

theorem tailTrace_1852278 : CollatzResearch.WordTrace tailWord_1852278 prefixEnd_1852278 951108919748809187506535 := by
  unfold tailWord_1852278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222383048970039046380343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45038752522347083161390325 4222383048970039046380343)
  ·
    refine ⟨6333574573455058569570515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4222383048970039046380343 6333574573455058569570515)
    ·
      refine ⟨9500361860182587854355773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6333574573455058569570515 9500361860182587854355773)
      ·
        refine ⟨3562635697568470445383415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9500361860182587854355773 3562635697568470445383415)
        ·
          refine ⟨5343953546352705668075123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562635697568470445383415 5343953546352705668075123)
          ·
            refine ⟨8015930319529058502112685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343953546352705668075123 8015930319529058502112685)
            ·
              refine ⟨3005973869823396938292257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8015930319529058502112685 3005973869823396938292257)
              ·
                refine ⟨2254480402367547703719193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005973869823396938292257 2254480402367547703719193)
                ·
                  refine ⟨1690860301775660777789395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254480402367547703719193 1690860301775660777789395)
                  ·
                    refine ⟨2536290452663491166684093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690860301775660777789395 2536290452663491166684093)
                    ·
                      refine ⟨951108919748809187506535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2536290452663491166684093 951108919748809187506535)
                      ·
                        rfl

theorem cell23_1852278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1852278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852278 prefixEnd_1852278 := by exact prefixLift 1852278
  have htrace : WordTrace (prefixWord ++ tailWord_1852278) baseStart_1852278 baseEnd_1852278 := by
    simpa [prefixWord, tailWord_1852278, baseEnd_1852278] using wordTrace_append hprefix tailTrace_1852278
  have hstable : (prefixWord ++ tailWord_1852278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852278).length < 2 ^ (prefixWord ++ tailWord_1852278).sum := by decide
  have hdescent : baseEnd_1852278 < baseStart_1852278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852297 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_1852297 : Nat := 118140960795 + 1852297 * 2 ^ 59
def prefixEnd_1852297 : Nat := 4983230072969 + 3 ^ 40 * 1852297 * 2
def baseEnd_1852297 : Nat := 951118675881244613168947

theorem tailTrace_1852297 : CollatzResearch.WordTrace tailWord_1852297 prefixEnd_1852297 951118675881244613168947 := by
  unfold tailWord_1852297
  simp only [CollatzResearch.WordTrace]
  refine ⟨67558821770451790987027145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45039214513634527324684763 67558821770451790987027145)
  ·
    refine ⟨50669116327838843240270359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67558821770451790987027145 50669116327838843240270359)
    ·
      refine ⟨76003674491758264860405539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50669116327838843240270359 76003674491758264860405539)
      ·
        refine ⟨114005511737637397290608309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76003674491758264860405539 114005511737637397290608309)
        ·
          refine ⟨10688016725403505995994529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114005511737637397290608309 10688016725403505995994529)
          ·
            refine ⟨8016012544052629496995897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10688016725403505995994529 8016012544052629496995897)
            ·
              refine ⟨6012009408039472122746923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8016012544052629496995897 6012009408039472122746923)
              ·
                refine ⟨9018014112059208184120385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012009408039472122746923 9018014112059208184120385)
                ·
                  refine ⟨6763510584044406138090289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9018014112059208184120385 6763510584044406138090289)
                  ·
                    refine ⟨5072632938033304603567717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6763510584044406138090289 5072632938033304603567717)
                    ·
                      refine ⟨951118675881244613168947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5072632938033304603567717 951118675881244613168947)
                      ·
                        rfl

theorem cell23_1852297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_1852297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852297 prefixEnd_1852297 := by exact prefixLift 1852297
  have htrace : WordTrace (prefixWord ++ tailWord_1852297) baseStart_1852297 baseEnd_1852297 := by
    simpa [prefixWord, tailWord_1852297, baseEnd_1852297] using wordTrace_append hprefix tailTrace_1852297
  have hstable : (prefixWord ++ tailWord_1852297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852297).length < 2 ^ (prefixWord ++ tailWord_1852297).sum := by decide
  have hdescent : baseEnd_1852297 < baseStart_1852297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852341 : List Nat := [1, 3, 3, 2, 1, 1, 5, 2, 5]
def baseStart_1852341 : Nat := 118140960795 + 1852341 * 2 ^ 59
def prefixEnd_1852341 : Nat := 4983230072969 + 3 ^ 40 * 1852341 * 2
def baseEnd_1852341 : Nat := 105682363225560271224305

theorem tailTrace_1852341 : CollatzResearch.WordTrace tailWord_1852341 prefixEnd_1852341 105682363225560271224305 := by
  unfold tailWord_1852341
  simp only [CollatzResearch.WordTrace]
  refine ⟨67560426582292386501628877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45040284388194924334419251 67560426582292386501628877)
  ·
    refine ⟨25335159968359644938110829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67560426582292386501628877 25335159968359644938110829)
    ·
      refine ⟨9500684988134866851791561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25335159968359644938110829 9500684988134866851791561)
      ·
        refine ⟨7125513741101150138843671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9500684988134866851791561 7125513741101150138843671)
        ·
          refine ⟨10688270611651725208265507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7125513741101150138843671 10688270611651725208265507)
          ·
            refine ⟨16032405917477587812398261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10688270611651725208265507 16032405917477587812398261)
            ·
              refine ⟨1503038054763523857412337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16032405917477587812398261 1503038054763523857412337)
              ·
                refine ⟨1127278541072642893059253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1503038054763523857412337 1127278541072642893059253)
                ·
                  refine ⟨105682363225560271224305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1127278541072642893059253 105682363225560271224305)
                  ·
                    rfl

theorem cell23_1852341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_1852341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852341 prefixEnd_1852341 := by exact prefixLift 1852341
  have htrace : WordTrace (prefixWord ++ tailWord_1852341) baseStart_1852341 baseEnd_1852341 := by
    simpa [prefixWord, tailWord_1852341, baseEnd_1852341] using wordTrace_append hprefix tailTrace_1852341
  have hstable : (prefixWord ++ tailWord_1852341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852341).length < 2 ^ (prefixWord ++ tailWord_1852341).sum := by decide
  have hdescent : baseEnd_1852341 < baseStart_1852341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852387 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1852387 : Nat := 118140960795 + 1852387 * 2 ^ 59
def prefixEnd_1852387 : Nat := 4983230072969 + 3 ^ 40 * 1852387 * 2
def baseEnd_1852387 : Nat := 951164889140149261043533

theorem tailTrace_1852387 : CollatzResearch.WordTrace tailWord_1852387 prefixEnd_1852387 951164889140149261043533 := by
  unfold tailWord_1852387
  simp only [CollatzResearch.WordTrace]
  refine ⟨67562104340125736357803415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45041402893417157571868943 67562104340125736357803415)
  ·
    refine ⟨101343156510188604536705123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67562104340125736357803415 101343156510188604536705123)
    ·
      refine ⟨152014734765282906805057685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101343156510188604536705123 152014734765282906805057685)
      ·
        refine ⟨7125690692122636256487079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152014734765282906805057685 7125690692122636256487079)
        ·
          refine ⟨10688536038183954384730619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7125690692122636256487079 10688536038183954384730619)
          ·
            refine ⟨16032804057275931577095929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10688536038183954384730619 16032804057275931577095929)
            ·
              refine ⟨12024603042956948682821947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16032804057275931577095929 12024603042956948682821947)
              ·
                refine ⟨18036904564435423024232921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12024603042956948682821947 18036904564435423024232921)
                ·
                  refine ⟨13527678423326567268174691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18036904564435423024232921 13527678423326567268174691)
                  ·
                    refine ⟨20291517634989850902262037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13527678423326567268174691 20291517634989850902262037)
                    ·
                      refine ⟨951164889140149261043533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20291517634989850902262037 951164889140149261043533)
                      ·
                        rfl

theorem cell23_1852387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1852387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852387 prefixEnd_1852387 := by exact prefixLift 1852387
  have htrace : WordTrace (prefixWord ++ tailWord_1852387) baseStart_1852387 baseEnd_1852387 := by
    simpa [prefixWord, tailWord_1852387, baseEnd_1852387] using wordTrace_append hprefix tailTrace_1852387
  have hstable : (prefixWord ++ tailWord_1852387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852387).length < 2 ^ (prefixWord ++ tailWord_1852387).sum := by decide
  have hdescent : baseEnd_1852387 < baseStart_1852387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852448 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 6]
def baseStart_1852448 : Nat := 118140960795 + 1852448 * 2 ^ 59
def prefixEnd_1852448 : Nat := 4983230072969 + 3 ^ 40 * 1852448 * 2
def baseEnd_1852448 : Nat := 105688467940008169153417

theorem tailTrace_1852448 : CollatzResearch.WordTrace tailWord_1852448 prefixEnd_1852448 105688467940008169153417 := by
  unfold tailWord_1852448
  simp only [CollatzResearch.WordTrace]
  refine ⟨33782164596452371887886999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45042886128603162517182665 33782164596452371887886999)
  ·
    refine ⟨50673246894678557831830499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33782164596452371887886999 50673246894678557831830499)
    ·
      refine ⟨76009870342017836747745749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50673246894678557831830499 76009870342017836747745749)
      ·
        refine ⟨1781481336141043048775291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 76009870342017836747745749 1781481336141043048775291)
        ·
          refine ⟨2672222004211564573162937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781481336141043048775291 2672222004211564573162937)
          ·
            refine ⟨2004166503158673429872203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2672222004211564573162937 2004166503158673429872203)
            ·
              refine ⟨3006249754738010144808305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004166503158673429872203 3006249754738010144808305)
              ·
                refine ⟨2254687316053507608606229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006249754738010144808305 2254687316053507608606229)
                ·
                  refine ⟨105688467940008169153417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2254687316053507608606229 105688467940008169153417)
                  ·
                    rfl

theorem cell23_1852448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 6].length) (baseStart_1852448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852448 prefixEnd_1852448 := by exact prefixLift 1852448
  have htrace : WordTrace (prefixWord ++ tailWord_1852448) baseStart_1852448 baseEnd_1852448 := by
    simpa [prefixWord, tailWord_1852448, baseEnd_1852448] using wordTrace_append hprefix tailTrace_1852448
  have hstable : (prefixWord ++ tailWord_1852448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852448).length < 2 ^ (prefixWord ++ tailWord_1852448).sum := by decide
  have hdescent : baseEnd_1852448 < baseStart_1852448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852468 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_1852468 : Nat := 118140960795 + 1852468 * 2 ^ 59
def prefixEnd_1852468 : Nat := 4983230072969 + 3 ^ 40 * 1852468 * 2
def baseEnd_1852468 : Nat := 951206481073163444130661

theorem tailTrace_1852468 : CollatzResearch.WordTrace tailWord_1852468 prefixEnd_1852468 951206481073163444130661 := by
  unfold tailWord_1852468
  simp only [CollatzResearch.WordTrace]
  refine ⟨33782529326416143595751029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45043372435221524794334705 33782529326416143595751029)
  ·
    refine ⟨3167112124351513462101659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33782529326416143595751029 3167112124351513462101659)
    ·
      refine ⟨4750668186527270193152489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167112124351513462101659 4750668186527270193152489)
      ·
        refine ⟨3563001139895452644864367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4750668186527270193152489 3563001139895452644864367)
        ·
          refine ⟨5344501709843178967296551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563001139895452644864367 5344501709843178967296551)
          ·
            refine ⟨8016752564764768450944827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344501709843178967296551 8016752564764768450944827)
            ·
              refine ⟨12025128847147152676417241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8016752564764768450944827 12025128847147152676417241)
              ·
                refine ⟨9018846635360364507312931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12025128847147152676417241 9018846635360364507312931)
                ·
                  refine ⟨13528269953040546760969397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018846635360364507312931 13528269953040546760969397)
                  ·
                    refine ⟨1268275308097551258840881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13528269953040546760969397 1268275308097551258840881)
                    ·
                      refine ⟨951206481073163444130661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268275308097551258840881 951206481073163444130661)
                      ·
                        rfl

theorem cell23_1852468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_1852468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852468 prefixEnd_1852468 := by exact prefixLift 1852468
  have htrace : WordTrace (prefixWord ++ tailWord_1852468) baseStart_1852468 baseEnd_1852468 := by
    simpa [prefixWord, tailWord_1852468, baseEnd_1852468] using wordTrace_append hprefix tailTrace_1852468
  have hstable : (prefixWord ++ tailWord_1852468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852468).length < 2 ^ (prefixWord ++ tailWord_1852468).sum := by decide
  have hdescent : baseEnd_1852468 < baseStart_1852468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852474 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_1852474 : Nat := 118140960795 + 1852474 * 2 ^ 59
def prefixEnd_1852474 : Nat := 4983230072969 + 3 ^ 40 * 1852474 * 2
def baseEnd_1852474 : Nat := 317069853985696806885211

theorem tailTrace_1852474 : CollatzResearch.WordTrace tailWord_1852474 prefixEnd_1852474 317069853985696806885211 := by
  unfold tailWord_1852474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891319372702637554055119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45043518327207033477480317 16891319372702637554055119)
  ·
    refine ⟨25336979059053956331082679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16891319372702637554055119 25336979059053956331082679)
    ·
      refine ⟨38005468588580934496624019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25336979059053956331082679 38005468588580934496624019)
      ·
        refine ⟨57008202882871401744936029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38005468588580934496624019 57008202882871401744936029)
        ·
          refine ⟨21378076081076775654351011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57008202882871401744936029 21378076081076775654351011)
          ·
            refine ⟨32067114121615163481526517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21378076081076775654351011 32067114121615163481526517)
            ·
              refine ⟨3006291948901421576393111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32067114121615163481526517 3006291948901421576393111)
              ·
                refine ⟨4509437923352132364589667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006291948901421576393111 4509437923352132364589667)
                ·
                  refine ⟨6764156885028198546884501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509437923352132364589667 6764156885028198546884501)
                  ·
                    refine ⟨317069853985696806885211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6764156885028198546884501 317069853985696806885211)
                    ·
                      rfl

theorem cell23_1852474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_1852474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852474 prefixEnd_1852474 := by exact prefixLift 1852474
  have htrace : WordTrace (prefixWord ++ tailWord_1852474) baseStart_1852474 baseEnd_1852474 := by
    simpa [prefixWord, tailWord_1852474, baseEnd_1852474] using wordTrace_append hprefix tailTrace_1852474
  have hstable : (prefixWord ++ tailWord_1852474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852474).length < 2 ^ (prefixWord ++ tailWord_1852474).sum := by decide
  have hdescent : baseEnd_1852474 < baseStart_1852474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852478 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1852478 : Nat := 118140960795 + 1852478 * 2 ^ 59
def prefixEnd_1852478 : Nat := 4983230072969 + 3 ^ 40 * 1852478 * 2
def baseEnd_1852478 : Nat := 317070538626569468335205

theorem tailTrace_1852478 : CollatzResearch.WordTrace tailWord_1852478 prefixEnd_1852478 317070538626569468335205 := by
  unfold tailWord_1852478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8445677922849507362420761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45043615588530705932910725 8445677922849507362420761)
  ·
    refine ⟨6334258442137130521815571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8445677922849507362420761 6334258442137130521815571)
    ·
      refine ⟨9501387663205695782723357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6334258442137130521815571 9501387663205695782723357)
      ·
        refine ⟨3563020373702135918521259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9501387663205695782723357 3563020373702135918521259)
        ·
          refine ⟨5344530560553203877781889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563020373702135918521259 5344530560553203877781889)
          ·
            refine ⟨4008397920414902908336417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5344530560553203877781889 4008397920414902908336417)
            ·
              refine ⟨3006298440311177181252313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4008397920414902908336417 3006298440311177181252313)
              ·
                refine ⟨2254723830233382885939235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006298440311177181252313 2254723830233382885939235)
                ·
                  refine ⟨3382085745350074328908853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254723830233382885939235 3382085745350074328908853)
                  ·
                    refine ⟨317070538626569468335205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3382085745350074328908853 317070538626569468335205)
                    ·
                      rfl

theorem cell23_1852478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1852478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852478 prefixEnd_1852478 := by exact prefixLift 1852478
  have htrace : WordTrace (prefixWord ++ tailWord_1852478) baseStart_1852478 baseEnd_1852478 := by
    simpa [prefixWord, tailWord_1852478, baseEnd_1852478] using wordTrace_append hprefix tailTrace_1852478
  have hstable : (prefixWord ++ tailWord_1852478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852478).length < 2 ^ (prefixWord ++ tailWord_1852478).sum := by decide
  have hdescent : baseEnd_1852478 < baseStart_1852478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852494 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1852494 : Nat := 118140960795 + 1852494 * 2 ^ 59
def prefixEnd_1852494 : Nat := 4983230072969 + 3 ^ 40 * 1852494 * 2
def baseEnd_1852494 : Nat := 951219831570180342405541

theorem tailTrace_1852494 : CollatzResearch.WordTrace tailWord_1852494 prefixEnd_1852494 951219831570180342405541 := by
  unfold tailWord_1852494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8445750868842261703993567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45044004633825395754632357 8445750868842261703993567)
  ·
    refine ⟨12668626303263392555990351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8445750868842261703993567 12668626303263392555990351)
    ·
      refine ⟨19002939454895088833985527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12668626303263392555990351 19002939454895088833985527)
      ·
        refine ⟨28504409182342633250978291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19002939454895088833985527 28504409182342633250978291)
        ·
          refine ⟨42756613773513949876467437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28504409182342633250978291 42756613773513949876467437)
          ·
            refine ⟨16033730165067731203675289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42756613773513949876467437 16033730165067731203675289)
            ·
              refine ⟨12025297623800798402756467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16033730165067731203675289 12025297623800798402756467)
              ·
                refine ⟨18037946435701197604134701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12025297623800798402756467 18037946435701197604134701)
                ·
                  refine ⟨6764229913387949101550513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18037946435701197604134701 6764229913387949101550513)
                  ·
                    refine ⟨5073172435040961826162885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6764229913387949101550513 5073172435040961826162885)
                    ·
                      refine ⟨951219831570180342405541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5073172435040961826162885 951219831570180342405541)
                      ·
                        rfl

theorem cell23_1852494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1852494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852494 prefixEnd_1852494 := by exact prefixLift 1852494
  have htrace : WordTrace (prefixWord ++ tailWord_1852494) baseStart_1852494 baseEnd_1852494 := by
    simpa [prefixWord, tailWord_1852494, baseEnd_1852494] using wordTrace_append hprefix tailTrace_1852494
  have hstable : (prefixWord ++ tailWord_1852494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852494).length < 2 ^ (prefixWord ++ tailWord_1852494).sum := by decide
  have hdescent : baseEnd_1852494 < baseStart_1852494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852501 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1852501 : Nat := 118140960795 + 1852501 * 2 ^ 59
def prefixEnd_1852501 : Nat := 4983230072969 + 3 ^ 40 * 1852501 * 2
def baseEnd_1852501 : Nat := 951223425934761815018009

theorem tailTrace_1852501 : CollatzResearch.WordTrace tailWord_1852501 prefixEnd_1852501 951223425934761815018009 := by
  unfold tailWord_1852501
  simp only [CollatzResearch.WordTrace]
  refine ⟨67566262261712733827453357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45044174841141822551635571 67566262261712733827453357)
  ·
    refine ⟨25337348348142275185295009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67566262261712733827453357 25337348348142275185295009)
    ·
      refine ⟨19003011261106706388971257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25337348348142275185295009 19003011261106706388971257)
      ·
        refine ⟨14252258445830029791728443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19003011261106706388971257 14252258445830029791728443)
        ·
          refine ⟨21378387668745044687592665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14252258445830029791728443 21378387668745044687592665)
          ·
            refine ⟨16033790751558783515694499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21378387668745044687592665 16033790751558783515694499)
            ·
              refine ⟨24050686127338175273541749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16033790751558783515694499 24050686127338175273541749)
              ·
                refine ⟨2254751824437953931894539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24050686127338175273541749 2254751824437953931894539)
                ·
                  refine ⟨3382127736656930897841809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254751824437953931894539 3382127736656930897841809)
                  ·
                    refine ⟨2536595802492698173381357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3382127736656930897841809 2536595802492698173381357)
                    ·
                      refine ⟨951223425934761815018009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2536595802492698173381357 951223425934761815018009)
                      ·
                        rfl

theorem cell23_1852501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1852501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852501 prefixEnd_1852501 := by exact prefixLift 1852501
  have htrace : WordTrace (prefixWord ++ tailWord_1852501) baseStart_1852501 baseEnd_1852501 := by
    simpa [prefixWord, tailWord_1852501, baseEnd_1852501] using wordTrace_append hprefix tailTrace_1852501
  have hstable : (prefixWord ++ tailWord_1852501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852501).length < 2 ^ (prefixWord ++ tailWord_1852501).sum := by decide
  have hdescent : baseEnd_1852501 < baseStart_1852501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852502 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1852502 : Nat := 118140960795 + 1852502 * 2 ^ 59
def prefixEnd_1852502 : Nat := 4983230072969 + 3 ^ 40 * 1852502 * 2
def baseEnd_1852502 : Nat := 951223939415416311105505

theorem tailTrace_1852502 : CollatzResearch.WordTrace tailWord_1852502 prefixEnd_1852502 951223939415416311105505 := by
  unfold tailWord_1852502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222893670919319437389985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45044199156472740665493173 4222893670919319437389985)
  ·
    refine ⟨3167170253189489578042489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4222893670919319437389985 3167170253189489578042489)
    ·
      refine ⟨2375377689892117183531867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3167170253189489578042489 2375377689892117183531867)
      ·
        refine ⟨3563066534838175775297801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375377689892117183531867 3563066534838175775297801)
        ·
          refine ⟨2672299901128631831473351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3563066534838175775297801 2672299901128631831473351)
          ·
            refine ⟨4008449851692947747210027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672299901128631831473351 4008449851692947747210027)
            ·
              refine ⟨6012674777539421620815041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008449851692947747210027 6012674777539421620815041)
              ·
                refine ⟨4509506083154566215611281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6012674777539421620815041 4509506083154566215611281)
                ·
                  refine ⟨3382129562365924661708461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4509506083154566215611281 3382129562365924661708461)
                  ·
                    refine ⟨1268298585887221748140673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382129562365924661708461 1268298585887221748140673)
                    ·
                      refine ⟨951223939415416311105505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268298585887221748140673 951223939415416311105505)
                      ·
                        rfl

theorem cell23_1852502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1852502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852502 prefixEnd_1852502 := by exact prefixLift 1852502
  have htrace : WordTrace (prefixWord ++ tailWord_1852502) baseStart_1852502 baseEnd_1852502 := by
    simpa [prefixWord, tailWord_1852502, baseEnd_1852502] using wordTrace_append hprefix tailTrace_1852502
  have hstable : (prefixWord ++ tailWord_1852502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852502).length < 2 ^ (prefixWord ++ tailWord_1852502).sum := by decide
  have hdescent : baseEnd_1852502 < baseStart_1852502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852509 : List Nat := [1, 4, 4, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1852509 : Nat := 118140960795 + 1852509 * 2 ^ 59
def prefixEnd_1852509 : Nat := 4983230072969 + 3 ^ 40 * 1852509 * 2
def baseEnd_1852509 : Nat := 951227533779997783717973

theorem tailTrace_1852509 : CollatzResearch.WordTrace tailWord_1852509 prefixEnd_1852509 951227533779997783717973 := by
  unfold tailWord_1852509
  simp only [CollatzResearch.WordTrace]
  refine ⟨67566554045683751193744581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45044369363789167462496387 67566554045683751193744581)
  ·
    refine ⟨12668728883565703348827109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67566554045683751193744581 12668728883565703348827109)
    ·
      refine ⟨2375386665668569377905083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12668728883565703348827109 2375386665668569377905083)
      ·
        refine ⟨3563079998502854066857625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375386665668569377905083 3563079998502854066857625)
        ·
          refine ⟨2672309998877140550143219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3563079998502854066857625 2672309998877140550143219)
          ·
            refine ⟨4008464998315710825214829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672309998877140550143219 4008464998315710825214829)
            ·
              refine ⟨1503174374368391559455561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4008464998315710825214829 1503174374368391559455561)
              ·
                refine ⟨1127380780776293669591671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1503174374368391559455561 1127380780776293669591671)
                ·
                  refine ⟨1691071171164440504387507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127380780776293669591671 1691071171164440504387507)
                  ·
                    refine ⟨2536606756746660756581261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1691071171164440504387507 2536606756746660756581261)
                    ·
                      refine ⟨951227533779997783717973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2536606756746660756581261 951227533779997783717973)
                      ·
                        rfl

theorem cell23_1852509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1852509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852509 prefixEnd_1852509 := by exact prefixLift 1852509
  have htrace : WordTrace (prefixWord ++ tailWord_1852509) baseStart_1852509 baseEnd_1852509 := by
    simpa [prefixWord, tailWord_1852509, baseEnd_1852509] using wordTrace_append hprefix tailTrace_1852509
  have hstable : (prefixWord ++ tailWord_1852509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852509).length < 2 ^ (prefixWord ++ tailWord_1852509).sum := by decide
  have hdescent : baseEnd_1852509 < baseStart_1852509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852525 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_1852525 : Nat := 118140960795 + 1852525 * 2 ^ 59
def prefixEnd_1852525 : Nat := 4983230072969 + 3 ^ 40 * 1852525 * 2
def baseEnd_1852525 : Nat := 317078583156823240372633

theorem tailTrace_1852525 : CollatzResearch.WordTrace tailWord_1852525 prefixEnd_1852525 317078583156823240372633 := by
  unfold tailWord_1852525
  simp only [CollatzResearch.WordTrace]
  refine ⟨67567137613625785926327029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45044758409083857284218019 67567137613625785926327029)
  ·
    refine ⟨6334419151277417430593159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67567137613625785926327029 6334419151277417430593159)
    ·
      refine ⟨9501628726916126145889739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6334419151277417430593159 9501628726916126145889739)
      ·
        refine ⟨14252443090374189218834609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9501628726916126145889739 14252443090374189218834609)
        ·
          refine ⟨10689332317780641914125957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14252443090374189218834609 10689332317780641914125957)
          ·
            refine ⟨2004249809583870358898617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10689332317780641914125957 2004249809583870358898617)
            ·
              refine ⟨1503187357187902769173963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004249809583870358898617 1503187357187902769173963)
              ·
                refine ⟨2254781035781854153760945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503187357187902769173963 2254781035781854153760945)
                ·
                  refine ⟨1691085776836390615320709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254781035781854153760945 1691085776836390615320709)
                  ·
                    refine ⟨317078583156823240372633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1691085776836390615320709 317078583156823240372633)
                    ·
                      rfl

theorem cell23_1852525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_1852525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852525 prefixEnd_1852525 := by exact prefixLift 1852525
  have htrace : WordTrace (prefixWord ++ tailWord_1852525) baseStart_1852525 baseEnd_1852525 := by
    simpa [prefixWord, tailWord_1852525, baseEnd_1852525] using wordTrace_append hprefix tailTrace_1852525
  have hstable : (prefixWord ++ tailWord_1852525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852525).length < 2 ^ (prefixWord ++ tailWord_1852525).sum := by decide
  have hdescent : baseEnd_1852525 < baseStart_1852525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852594 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 9]
def baseStart_1852594 : Nat := 118140960795 + 1852594 * 2 ^ 59
def prefixEnd_1852594 : Nat := 4983230072969 + 3 ^ 40 * 1852594 * 2
def baseEnd_1852594 : Nat := 105696797737292216795009

theorem tailTrace_1852594 : CollatzResearch.WordTrace tailWord_1852594 prefixEnd_1852594 105696797737292216795009 := by
  unfold tailWord_1852594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16892413562593952677647209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45046436166917207140392557 16892413562593952677647209)
  ·
    refine ⟨12669310171945464508235407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16892413562593952677647209 12669310171945464508235407)
    ·
      refine ⟨19003965257918196762353111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12669310171945464508235407 19003965257918196762353111)
      ·
        refine ⟨28505947886877295143529667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19003965257918196762353111 28505947886877295143529667)
        ·
          refine ⟨42758921830315942715294501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28505947886877295143529667 42758921830315942715294501)
          ·
            refine ⟨8017297843184239259117719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42758921830315942715294501 8017297843184239259117719)
            ·
              refine ⟨12025946764776358888676579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8017297843184239259117719 12025946764776358888676579)
              ·
                refine ⟨18038920147164538333014869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12025946764776358888676579 18038920147164538333014869)
                ·
                  refine ⟨105696797737292216795009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18038920147164538333014869 105696797737292216795009)
                  ·
                    rfl

theorem cell23_1852594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_1852594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852594 prefixEnd_1852594 := by exact prefixLift 1852594
  have htrace : WordTrace (prefixWord ++ tailWord_1852594) baseStart_1852594 baseEnd_1852594 := by
    simpa [prefixWord, tailWord_1852594, baseEnd_1852594] using wordTrace_append hprefix tailTrace_1852594
  have hstable : (prefixWord ++ tailWord_1852594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852594).length < 2 ^ (prefixWord ++ tailWord_1852594).sum := by decide
  have hdescent : baseEnd_1852594 < baseStart_1852594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852609 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_1852609 : Nat := 118140960795 + 1852609 * 2 ^ 59
def prefixEnd_1852609 : Nat := 4983230072969 + 3 ^ 40 * 1852609 * 2
def baseEnd_1852609 : Nat := 951278881845447392467513

theorem tailTrace_1852609 : CollatzResearch.WordTrace tailWord_1852609 prefixEnd_1852609 951278881845447392467513 := by
  unfold tailWord_1852609
  simp only [CollatzResearch.WordTrace]
  refine ⟨67570201345321468272384881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45046800896880978848256587 67570201345321468272384881)
  ·
    refine ⟨50677651008991101204288661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67570201345321468272384881 50677651008991101204288661)
    ·
      refine ⟨2375514891046457868951031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50677651008991101204288661 2375514891046457868951031)
      ·
        refine ⟨3563272336569686803426547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375514891046457868951031 3563272336569686803426547)
        ·
          refine ⟨5344908504854530205139821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563272336569686803426547 5344908504854530205139821)
          ·
            refine ⟨2004340689320448826927433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5344908504854530205139821 2004340689320448826927433)
            ·
              refine ⟨1503255516990336620195575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004340689320448826927433 1503255516990336620195575)
              ·
                refine ⟨2254883275485504930293363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503255516990336620195575 2254883275485504930293363)
                ·
                  refine ⟨3382324913228257395440045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254883275485504930293363 3382324913228257395440045)
                  ·
                    refine ⟨1268371842460596523290017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382324913228257395440045 1268371842460596523290017)
                    ·
                      refine ⟨951278881845447392467513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268371842460596523290017 951278881845447392467513)
                      ·
                        rfl

theorem cell23_1852609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_1852609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852609 prefixEnd_1852609 := by exact prefixLift 1852609
  have htrace : WordTrace (prefixWord ++ tailWord_1852609) baseStart_1852609 baseEnd_1852609 := by
    simpa [prefixWord, tailWord_1852609, baseEnd_1852609] using wordTrace_append hprefix tailTrace_1852609
  have hstable : (prefixWord ++ tailWord_1852609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852609).length < 2 ^ (prefixWord ++ tailWord_1852609).sum := by decide
  have hdescent : baseEnd_1852609 < baseStart_1852609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852631 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 7, 2]
def baseStart_1852631 : Nat := 118140960795 + 1852631 * 2 ^ 59
def prefixEnd_1852631 : Nat := 4983230072969 + 3 ^ 40 * 1852631 * 2
def baseEnd_1852631 : Nat := 951290178419846306392411

theorem tailTrace_1852631 : CollatzResearch.WordTrace tailWord_1852631 prefixEnd_1852631 951290178419846306392411 := by
  unfold tailWord_1852631
  simp only [CollatzResearch.WordTrace]
  refine ⟨67571003751241766029685747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45047335834161177353123831 67571003751241766029685747)
  ·
    refine ⟨101356505626862649044528621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67571003751241766029685747 101356505626862649044528621)
    ·
      refine ⟨38008689610073493391698233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101356505626862649044528621 38008689610073493391698233)
      ·
        refine ⟨28506517207555120043773675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38008689610073493391698233 28506517207555120043773675)
        ·
          refine ⟨42759775811332680065660513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28506517207555120043773675 42759775811332680065660513)
          ·
            refine ⟨32069831858499510049245385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42759775811332680065660513 32069831858499510049245385)
            ·
              refine ⟨24052373893874632536934039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32069831858499510049245385 24052373893874632536934039)
              ·
                refine ⟨36078560840811948805401059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24052373893874632536934039 36078560840811948805401059)
                ·
                  refine ⟨54117841261217923208101589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36078560840811948805401059 54117841261217923208101589)
                  ·
                    refine ⟨1268386904559795075189881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54117841261217923208101589 1268386904559795075189881)
                    ·
                      refine ⟨951290178419846306392411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268386904559795075189881 951290178419846306392411)
                      ·
                        rfl

theorem cell23_1852631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_1852631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852631 prefixEnd_1852631 := by exact prefixLift 1852631
  have htrace : WordTrace (prefixWord ++ tailWord_1852631) baseStart_1852631 baseEnd_1852631 := by
    simpa [prefixWord, tailWord_1852631, baseEnd_1852631] using wordTrace_append hprefix tailTrace_1852631
  have hstable : (prefixWord ++ tailWord_1852631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852631).length < 2 ^ (prefixWord ++ tailWord_1852631).sum := by decide
  have hdescent : baseEnd_1852631 < baseStart_1852631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852634 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1852634 : Nat := 118140960795 + 1852634 * 2 ^ 59
def prefixEnd_1852634 : Nat := 4983230072969 + 3 ^ 40 * 1852634 * 2
def baseEnd_1852634 : Nat := 951291718861809794654897

theorem tailTrace_1852634 : CollatzResearch.WordTrace tailWord_1852634 prefixEnd_1852634 951291718861809794654897 := by
  unfold tailWord_1852634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16892778292557724385511239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45047408780153931694696637 16892778292557724385511239)
  ·
    refine ⟨25339167438836586578266859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16892778292557724385511239 25339167438836586578266859)
    ·
      refine ⟨38008751158254879867400289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25339167438836586578266859 38008751158254879867400289)
      ·
        refine ⟨28506563368691159900550217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38008751158254879867400289 28506563368691159900550217)
        ·
          refine ⟨21379922526518369925412663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28506563368691159900550217 21379922526518369925412663)
          ·
            refine ⟨32069883789777554888118995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21379922526518369925412663 32069883789777554888118995)
            ·
              refine ⟨48104825684666332332178493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32069883789777554888118995 48104825684666332332178493)
              ·
                refine ⟨18039309631749874624566935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48104825684666332332178493 18039309631749874624566935)
                ·
                  refine ⟨27058964447624811936850403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18039309631749874624566935 27058964447624811936850403)
                  ·
                    refine ⟨40588446671437217905275605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27058964447624811936850403 40588446671437217905275605)
                    ·
                      refine ⟨951291718861809794654897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40588446671437217905275605 951291718861809794654897)
                      ·
                        rfl

theorem cell23_1852634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1852634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852634 prefixEnd_1852634 := by exact prefixLift 1852634
  have htrace : WordTrace (prefixWord ++ tailWord_1852634) baseStart_1852634 baseEnd_1852634 := by
    simpa [prefixWord, tailWord_1852634, baseEnd_1852634] using wordTrace_append hprefix tailTrace_1852634
  have hstable : (prefixWord ++ tailWord_1852634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852634).length < 2 ^ (prefixWord ++ tailWord_1852634).sum := by decide
  have hdescent : baseEnd_1852634 < baseStart_1852634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852664 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_1852664 : Nat := 118140960795 + 1852664 * 2 ^ 59
def prefixEnd_1852664 : Nat := 4983230072969 + 3 ^ 40 * 1852664 * 2
def baseEnd_1852664 : Nat := 951307123281444677279759

theorem tailTrace_1852664 : CollatzResearch.WordTrace tailWord_1852664 prefixEnd_1852664 951307123281444677279759 := by
  unfold tailWord_1852664
  simp only [CollatzResearch.WordTrace]
  refine ⟨33786103680061106332818523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45048138240081475110424697 33786103680061106332818523)
  ·
    refine ⟨50679155520091659499227785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33786103680061106332818523 50679155520091659499227785)
    ·
      refine ⟨38009366640068744624420839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50679155520091659499227785 38009366640068744624420839)
      ·
        refine ⟨57014049960103116936631259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38009366640068744624420839 57014049960103116936631259)
        ·
          refine ⟨85521074940154675404946889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57014049960103116936631259 85521074940154675404946889)
          ·
            refine ⟨64140806205116006553710167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85521074940154675404946889 64140806205116006553710167)
            ·
              refine ⟨96211209307674009830565251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64140806205116006553710167 96211209307674009830565251)
              ·
                refine ⟨144316813961511014745847877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96211209307674009830565251 144316813961511014745847877)
                ·
                  refine ⟨27059402617783315264846477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144316813961511014745847877 27059402617783315264846477)
                  ·
                    refine ⟨10147275981668743224317429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27059402617783315264846477 10147275981668743224317429)
                    ·
                      refine ⟨951307123281444677279759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10147275981668743224317429 951307123281444677279759)
                      ·
                        rfl

theorem cell23_1852664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_1852664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852664 prefixEnd_1852664 := by exact prefixLift 1852664
  have htrace : WordTrace (prefixWord ++ tailWord_1852664) baseStart_1852664 baseEnd_1852664 := by
    simpa [prefixWord, tailWord_1852664, baseEnd_1852664] using wordTrace_append hprefix tailTrace_1852664
  have hstable : (prefixWord ++ tailWord_1852664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852664).length < 2 ^ (prefixWord ++ tailWord_1852664).sum := by decide
  have hdescent : baseEnd_1852664 < baseStart_1852664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852761 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 1, 6]
def baseStart_1852761 : Nat := 118140960795 + 1852761 * 2 ^ 59
def prefixEnd_1852761 : Nat := 4983230072969 + 3 ^ 40 * 1852761 * 2
def baseEnd_1852761 : Nat := 317118976968310265922271

theorem tailTrace_1852761 : CollatzResearch.WordTrace tailWord_1852761 prefixEnd_1852761 317118976968310265922271 := by
  unfold tailWord_1852761
  simp only [CollatzResearch.WordTrace]
  refine ⟨67575745240770798231918137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45050496827180532154612091 67575745240770798231918137)
  ·
    refine ⟨50681808930578098673938603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67575745240770798231918137 50681808930578098673938603)
    ·
      refine ⟨76022713395867148010907905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50681808930578098673938603 76022713395867148010907905)
      ·
        refine ⟨57017035046900361008180929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76022713395867148010907905 57017035046900361008180929)
        ·
          refine ⟨42762776285175270756135697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57017035046900361008180929 42762776285175270756135697)
          ·
            refine ⟨32072082213881453067101773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42762776285175270756135697 32072082213881453067101773)
            ·
              refine ⟨12027030830205544900163165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32072082213881453067101773 12027030830205544900163165)
              ·
                refine ⟨4510136561327079337561187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12027030830205544900163165 4510136561327079337561187)
                ·
                  refine ⟨6765204841990619006341781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510136561327079337561187 6765204841990619006341781)
                  ·
                    refine ⟨317118976968310265922271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6765204841990619006341781 317118976968310265922271)
                    ·
                      rfl

theorem cell23_1852761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_1852761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852761 prefixEnd_1852761 := by exact prefixLift 1852761
  have htrace : WordTrace (prefixWord ++ tailWord_1852761) baseStart_1852761 baseEnd_1852761 := by
    simpa [prefixWord, tailWord_1852761, baseEnd_1852761] using wordTrace_append hprefix tailTrace_1852761
  have hstable : (prefixWord ++ tailWord_1852761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852761).length < 2 ^ (prefixWord ++ tailWord_1852761).sum := by decide
  have hdescent : baseEnd_1852761 < baseStart_1852761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852768 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1852768 : Nat := 118140960795 + 1852768 * 2 ^ 59
def prefixEnd_1852768 : Nat := 4983230072969 + 3 ^ 40 * 1852768 * 2
def baseEnd_1852768 : Nat := 951360525269512270379281

theorem tailTrace_1852768 : CollatzResearch.WordTrace tailWord_1852768 prefixEnd_1852768 951360525269512270379281 := by
  unfold tailWord_1852768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33788000275872719213711479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45050667034496958951615305 33788000275872719213711479)
  ·
    refine ⟨50682000413809078820567219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33788000275872719213711479 50682000413809078820567219)
    ·
      refine ⟨76023000620713618230850829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50682000413809078820567219 76023000620713618230850829)
      ·
        refine ⟨28508625232767606836569061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76023000620713618230850829 28508625232767606836569061)
        ·
          refine ⟨5345367231143926281856699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28508625232767606836569061 5345367231143926281856699)
          ·
            refine ⟨8018050846715889422785049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345367231143926281856699 8018050846715889422785049)
            ·
              refine ⟨6013538135036917067088787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8018050846715889422785049 6013538135036917067088787)
              ·
                refine ⟨9020307202555375600633181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6013538135036917067088787 9020307202555375600633181)
                ·
                  refine ⟨3382615200958265850237443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9020307202555375600633181 3382615200958265850237443)
                  ·
                    refine ⟨5073922801437398775356165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382615200958265850237443 5073922801437398775356165)
                    ·
                      refine ⟨951360525269512270379281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5073922801437398775356165 951360525269512270379281)
                      ·
                        rfl

theorem cell23_1852768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1852768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852768 prefixEnd_1852768 := by exact prefixLift 1852768
  have htrace : WordTrace (prefixWord ++ tailWord_1852768) baseStart_1852768 baseEnd_1852768 := by
    simpa [prefixWord, tailWord_1852768, baseEnd_1852768] using wordTrace_append hprefix tailTrace_1852768
  have hstable : (prefixWord ++ tailWord_1852768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852768).length < 2 ^ (prefixWord ++ tailWord_1852768).sum := by decide
  have hdescent : baseEnd_1852768 < baseStart_1852768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852772 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_1852772 : Nat := 118140960795 + 1852772 * 2 ^ 59
def prefixEnd_1852772 : Nat := 4983230072969 + 3 ^ 40 * 1852772 * 2
def baseEnd_1852772 : Nat := 951362579192130254729263

theorem tailTrace_1852772 : CollatzResearch.WordTrace tailWord_1852772 prefixEnd_1852772 951362579192130254729263 := by
  unfold tailWord_1852772
  simp only [CollatzResearch.WordTrace]
  refine ⟨33788073221865473555284285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45050764295820631407045713 33788073221865473555284285)
  ·
    refine ⟨12670527458199552583231607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33788073221865473555284285 12670527458199552583231607)
    ·
      refine ⟨19005791187299328874847411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12670527458199552583231607 19005791187299328874847411)
      ·
        refine ⟨28508686780948993312271117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19005791187299328874847411 28508686780948993312271117)
        ·
          refine ⟨10690757542855872492101669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28508686780948993312271117 10690757542855872492101669)
          ·
            refine ⟨2004517039285476092269063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10690757542855872492101669 2004517039285476092269063)
            ·
              refine ⟨3006775558928214138403595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004517039285476092269063 3006775558928214138403595)
              ·
                refine ⟨4510163338392321207605393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006775558928214138403595 4510163338392321207605393)
                ·
                  refine ⟨3382622503794240905704045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510163338392321207605393 3382622503794240905704045)
                  ·
                    refine ⟨1268483438922840339639017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382622503794240905704045 1268483438922840339639017)
                    ·
                      refine ⟨951362579192130254729263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268483438922840339639017 951362579192130254729263)
                      ·
                        rfl

theorem cell23_1852772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_1852772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852772 prefixEnd_1852772 := by exact prefixLift 1852772
  have htrace : WordTrace (prefixWord ++ tailWord_1852772) baseStart_1852772 baseEnd_1852772 := by
    simpa [prefixWord, tailWord_1852772, baseEnd_1852772] using wordTrace_append hprefix tailTrace_1852772
  have hstable : (prefixWord ++ tailWord_1852772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852772).length < 2 ^ (prefixWord ++ tailWord_1852772).sum := by decide
  have hdescent : baseEnd_1852772 < baseStart_1852772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852782 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1852782 : Nat := 118140960795 + 1852782 * 2 ^ 59
def prefixEnd_1852782 : Nat := 4983230072969 + 3 ^ 40 * 1852782 * 2
def baseEnd_1852782 : Nat := 317122571332891738534739

theorem tailTrace_1852782 : CollatzResearch.WordTrace tailWord_1852782 prefixEnd_1852782 317122571332891738534739 := by
  unfold tailWord_1852782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447063896711839852304075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45051007449129812545621733 8447063896711839852304075)
  ·
    refine ⟨12670595845067759778456113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8447063896711839852304075 12670595845067759778456113)
    ·
      refine ⟨9502946883800819833842085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12670595845067759778456113 9502946883800819833842085)
      ·
        refine ⟨1781802540712653718845391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9502946883800819833842085 1781802540712653718845391)
        ·
          refine ⟨2672703811068980578268087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781802540712653718845391 2672703811068980578268087)
          ·
            refine ⟨4009055716603470867402131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672703811068980578268087 4009055716603470867402131)
            ·
              refine ⟨6013583574905206301103197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009055716603470867402131 6013583574905206301103197)
              ·
                refine ⟨2255093840589452362913699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6013583574905206301103197 2255093840589452362913699)
                ·
                  refine ⟨3382640760884178544370549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255093840589452362913699 3382640760884178544370549)
                  ·
                    refine ⟨317122571332891738534739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3382640760884178544370549 317122571332891738534739)
                    ·
                      rfl

theorem cell23_1852782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1852782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852782 prefixEnd_1852782 := by exact prefixLift 1852782
  have htrace : WordTrace (prefixWord ++ tailWord_1852782) baseStart_1852782 baseEnd_1852782 := by
    simpa [prefixWord, tailWord_1852782, baseEnd_1852782] using wordTrace_append hprefix tailTrace_1852782
  have hstable : (prefixWord ++ tailWord_1852782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852782).length < 2 ^ (prefixWord ++ tailWord_1852782).sum := by decide
  have hdescent : baseEnd_1852782 < baseStart_1852782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852785 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 1, 1, 4]
def baseStart_1852785 : Nat := 118140960795 + 1852785 * 2 ^ 59
def prefixEnd_1852785 : Nat := 4983230072969 + 3 ^ 40 * 1852785 * 2
def baseEnd_1852785 : Nat := 951369254440638703866703

theorem tailTrace_1852785 : CollatzResearch.WordTrace tailWord_1852785 prefixEnd_1852785 951369254440638703866703 := by
  unfold tailWord_1852785
  simp only [CollatzResearch.WordTrace]
  refine ⟨67576620592683850330791809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45051080395122566887194539 67576620592683850330791809)
  ·
    refine ⟨50682465444512887748093857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67576620592683850330791809 50682465444512887748093857)
    ·
      refine ⟨38011849083384665811070393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50682465444512887748093857 38011849083384665811070393)
      ·
        refine ⟨28508886812538499358302795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38011849083384665811070393 28508886812538499358302795)
        ·
          refine ⟨42763330218807749037454193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28508886812538499358302795 42763330218807749037454193)
          ·
            refine ⟨32072497664105811778090645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42763330218807749037454193 32072497664105811778090645)
            ·
              refine ⟨1503398328004959927097999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32072497664105811778090645 1503398328004959927097999)
              ·
                refine ⟨2255097492007439890646999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503398328004959927097999 2255097492007439890646999)
                ·
                  refine ⟨3382646238011159835970499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255097492007439890646999 3382646238011159835970499)
                  ·
                    refine ⟨5073969357016739753955749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382646238011159835970499 5073969357016739753955749)
                    ·
                      refine ⟨951369254440638703866703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5073969357016739753955749 951369254440638703866703)
                      ·
                        rfl

theorem cell23_1852785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_1852785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852785 prefixEnd_1852785 := by exact prefixLift 1852785
  have htrace : WordTrace (prefixWord ++ tailWord_1852785) baseStart_1852785 baseEnd_1852785 := by
    simpa [prefixWord, tailWord_1852785, baseEnd_1852785] using wordTrace_append hprefix tailTrace_1852785
  have hstable : (prefixWord ++ tailWord_1852785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852785).length < 2 ^ (prefixWord ++ tailWord_1852785).sum := by decide
  have hdescent : baseEnd_1852785 < baseStart_1852785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852821 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_1852821 : Nat := 118140960795 + 1852821 * 2 ^ 59
def prefixEnd_1852821 : Nat := 4983230072969 + 3 ^ 40 * 1852821 * 2
def baseEnd_1852821 : Nat := 317129246581400187672179

theorem tailTrace_1852821 : CollatzResearch.WordTrace tailWord_1852821 prefixEnd_1852821 317129246581400187672179 := by
  unfold tailWord_1852821
  simp only [CollatzResearch.WordTrace]
  refine ⟨67577933620553428479102317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45051955747035618986068211 67577933620553428479102317)
  ·
    refine ⟨25341725107707535679663369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67577933620553428479102317 25341725107707535679663369)
    ·
      refine ⟨19006293830780651759747527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25341725107707535679663369 19006293830780651759747527)
      ·
        refine ⟨28509440746170977639621291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19006293830780651759747527 28509440746170977639621291)
        ·
          refine ⟨42764161119256466459431937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28509440746170977639621291 42764161119256466459431937)
          ·
            refine ⟨32073120839442349844573953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42764161119256466459431937 32073120839442349844573953)
            ·
              refine ⟨24054840629581762383430465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32073120839442349844573953 24054840629581762383430465)
              ·
                refine ⟨18041130472186321787572849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24054840629581762383430465 18041130472186321787572849)
                ·
                  refine ⟨13530847854139741340679637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18041130472186321787572849 13530847854139741340679637)
                  ·
                    refine ⟨317129246581400187672179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13530847854139741340679637 317129246581400187672179)
                    ·
                      rfl

theorem cell23_1852821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_1852821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852821 prefixEnd_1852821 := by exact prefixLift 1852821
  have htrace : WordTrace (prefixWord ++ tailWord_1852821) baseStart_1852821 baseEnd_1852821 := by
    simpa [prefixWord, tailWord_1852821, baseEnd_1852821] using wordTrace_append hprefix tailTrace_1852821
  have hstable : (prefixWord ++ tailWord_1852821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852821).length < 2 ^ (prefixWord ++ tailWord_1852821).sum := by decide
  have hdescent : baseEnd_1852821 < baseStart_1852821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852841 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_1852841 : Nat := 118140960795 + 1852841 * 2 ^ 59
def prefixEnd_1852841 : Nat := 4983230072969 + 3 ^ 40 * 1852841 * 2
def baseEnd_1852841 : Nat := 951398009357290484766445

theorem tailTrace_1852841 : CollatzResearch.WordTrace tailWord_1852841 prefixEnd_1852841 951398009357290484766445 := by
  unfold tailWord_1852841
  simp only [CollatzResearch.WordTrace]
  refine ⟨67578663080480971894830377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45052442053653981263220251 67578663080480971894830377)
  ·
    refine ⟨50683997310360728921122783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67578663080480971894830377 50683997310360728921122783)
    ·
      refine ⟨76025995965541093381684175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50683997310360728921122783 76025995965541093381684175)
      ·
        refine ⟨114038993948311640072526263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76025995965541093381684175 114038993948311640072526263)
        ·
          refine ⟨171058490922467460108789395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114038993948311640072526263 171058490922467460108789395)
          ·
            refine ⟨256587736383701190163184093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171058490922467460108789395 256587736383701190163184093)
            ·
              refine ⟨96220401143887946311194035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256587736383701190163184093 96220401143887946311194035)
              ·
                refine ⟨144330601715831919466791053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96220401143887946311194035 144330601715831919466791053)
                ·
                  refine ⟨54123975643436969800046645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144330601715831919466791053 54123975643436969800046645)
                  ·
                    refine ⟨5074122716572215918754373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54123975643436969800046645 5074122716572215918754373)
                    ·
                      refine ⟨951398009357290484766445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5074122716572215918754373 951398009357290484766445)
                      ·
                        rfl

theorem cell23_1852841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_1852841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852841 prefixEnd_1852841 := by exact prefixLift 1852841
  have htrace : WordTrace (prefixWord ++ tailWord_1852841) baseStart_1852841 baseEnd_1852841 := by
    simpa [prefixWord, tailWord_1852841, baseEnd_1852841] using wordTrace_append hprefix tailTrace_1852841
  have hstable : (prefixWord ++ tailWord_1852841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852841).length < 2 ^ (prefixWord ++ tailWord_1852841).sum := by decide
  have hdescent : baseEnd_1852841 < baseStart_1852841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852851 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 4, 6]
def baseStart_1852851 : Nat := 118140960795 + 1852851 * 2 ^ 59
def prefixEnd_1852851 : Nat := 4983230072969 + 3 ^ 40 * 1852851 * 2
def baseEnd_1852851 : Nat := 317134381387945148547133

theorem tailTrace_1852851 : CollatzResearch.WordTrace tailWord_1852851 prefixEnd_1852851 317134381387945148547133 := by
  unfold tailWord_1852851
  simp only [CollatzResearch.WordTrace]
  refine ⟨67579027810444743602694407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45052685206963162401796271 67579027810444743602694407)
  ·
    refine ⟨101368541715667115404041611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67579027810444743602694407 101368541715667115404041611)
    ·
      refine ⟨152052812573500673106062417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101368541715667115404041611 152052812573500673106062417)
      ·
        refine ⟨114039609430125504829546813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152052812573500673106062417 114039609430125504829546813)
        ·
          refine ⟨42764853536297064311080055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114039609430125504829546813 42764853536297064311080055)
          ·
            refine ⟨64147280304445596466620083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42764853536297064311080055 64147280304445596466620083)
            ·
              refine ⟨96220920456668394699930125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64147280304445596466620083 96220920456668394699930125)
              ·
                refine ⟨36082845171250648012473797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96220920456668394699930125 36082845171250648012473797)
                ·
                  refine ⟨6765533469609496502338837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36082845171250648012473797 6765533469609496502338837)
                  ·
                    refine ⟨317134381387945148547133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6765533469609496502338837 317134381387945148547133)
                    ·
                      rfl

theorem cell23_1852851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 6].length) (baseStart_1852851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852851 prefixEnd_1852851 := by exact prefixLift 1852851
  have htrace : WordTrace (prefixWord ++ tailWord_1852851) baseStart_1852851 baseEnd_1852851 := by
    simpa [prefixWord, tailWord_1852851, baseEnd_1852851] using wordTrace_append hprefix tailTrace_1852851
  have hstable : (prefixWord ++ tailWord_1852851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852851).length < 2 ^ (prefixWord ++ tailWord_1852851).sum := by decide
  have hdescent : baseEnd_1852851 < baseStart_1852851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852878 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1852878 : Nat := 118140960795 + 1852878 * 2 ^ 59
def prefixEnd_1852878 : Nat := 4983230072969 + 3 ^ 40 * 1852878 * 2
def baseEnd_1852878 : Nat := 951417008141506840003775

theorem tailTrace_1852878 : CollatzResearch.WordTrace tailWord_1852878 prefixEnd_1852878 951417008141506840003775 := by
  unfold tailWord_1852878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447501572668365901740911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45053341720897951475951525 8447501572668365901740911)
  ·
    refine ⟨12671252359002548852611367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8447501572668365901740911 12671252359002548852611367)
    ·
      refine ⟨19006878538503823278917051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671252359002548852611367 19006878538503823278917051)
      ·
        refine ⟨28510317807755734918375577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19006878538503823278917051 28510317807755734918375577)
        ·
          refine ⟨21382738355816801188781683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28510317807755734918375577 21382738355816801188781683)
          ·
            refine ⟨32074107533725201783172525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21382738355816801188781683 32074107533725201783172525)
            ·
              refine ⟨12027790325146950668689697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32074107533725201783172525 12027790325146950668689697)
              ·
                refine ⟨9020842743860213001517273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12027790325146950668689697 9020842743860213001517273)
                ·
                  refine ⟨6765632057895159751137955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9020842743860213001517273 6765632057895159751137955)
                  ·
                    refine ⟨10148448086842739626706933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6765632057895159751137955 10148448086842739626706933)
                    ·
                      refine ⟨951417008141506840003775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10148448086842739626706933 951417008141506840003775)
                      ·
                        rfl

theorem cell23_1852878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1852878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852878 prefixEnd_1852878 := by exact prefixLift 1852878
  have htrace : WordTrace (prefixWord ++ tailWord_1852878) baseStart_1852878 baseEnd_1852878 := by
    simpa [prefixWord, tailWord_1852878, baseEnd_1852878] using wordTrace_append hprefix tailTrace_1852878
  have hstable : (prefixWord ++ tailWord_1852878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852878).length < 2 ^ (prefixWord ++ tailWord_1852878).sum := by decide
  have hdescent : baseEnd_1852878 < baseStart_1852878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852925 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_1852925 : Nat := 118140960795 + 1852925 * 2 ^ 59
def prefixEnd_1852925 : Nat := 4983230072969 + 3 ^ 40 * 1852925 * 2
def baseEnd_1852925 : Nat := 951441141732268156116059

theorem tailTrace_1852925 : CollatzResearch.WordTrace tailWord_1852925 prefixEnd_1852925 951441141732268156116059 := by
  unfold tailWord_1852925
  simp only [CollatzResearch.WordTrace]
  refine ⟨67581726812176654240888229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45054484541451102827258819 67581726812176654240888229)
  ·
    refine ⟨12671573777283122670166543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67581726812176654240888229 12671573777283122670166543)
    ·
      refine ⟨19007360665924684005249815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671573777283122670166543 19007360665924684005249815)
      ·
        refine ⟨28511040998887026007874723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19007360665924684005249815 28511040998887026007874723)
        ·
          refine ⟨42766561498330539011812085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28511040998887026007874723 42766561498330539011812085)
          ·
            refine ⟨4009365140468488032357383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42766561498330539011812085 4009365140468488032357383)
            ·
              refine ⟨6014047710702732048536075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009365140468488032357383 6014047710702732048536075)
              ·
                refine ⟨9021071566054098072804113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014047710702732048536075 9021071566054098072804113)
                ·
                  refine ⟨6765803674540573554603085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9021071566054098072804113 6765803674540573554603085)
                  ·
                    refine ⟨2537176377952715082976157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6765803674540573554603085 2537176377952715082976157)
                    ·
                      refine ⟨951441141732268156116059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537176377952715082976157 951441141732268156116059)
                      ·
                        rfl

theorem cell23_1852925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_1852925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852925 prefixEnd_1852925 := by exact prefixLift 1852925
  have htrace : WordTrace (prefixWord ++ tailWord_1852925) baseStart_1852925 baseEnd_1852925 := by
    simpa [prefixWord, tailWord_1852925, baseEnd_1852925] using wordTrace_append hprefix tailTrace_1852925
  have hstable : (prefixWord ++ tailWord_1852925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852925).length < 2 ^ (prefixWord ++ tailWord_1852925).sum := by decide
  have hdescent : baseEnd_1852925 < baseStart_1852925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852926 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1852926 : Nat := 118140960795 + 1852926 * 2 ^ 59
def prefixEnd_1852926 : Nat := 4983230072969 + 3 ^ 40 * 1852926 * 2
def baseEnd_1852926 : Nat := 951441655212922652203555

theorem tailTrace_1852926 : CollatzResearch.WordTrace tailWord_1852926 prefixEnd_1852926 951441655212922652203555 := by
  unfold tailWord_1852926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8447720410646628926459329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45054508856782020941116421 8447720410646628926459329)
  ·
    refine ⟨6335790307984971694844497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8447720410646628926459329 6335790307984971694844497)
    ·
      refine ⟨4751842730988728771133373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6335790307984971694844497 4751842730988728771133373)
      ·
        refine ⟨1781941024120773289175015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4751842730988728771133373 1781941024120773289175015)
        ·
          refine ⟨2672911536181159933762523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781941024120773289175015 2672911536181159933762523)
          ·
            refine ⟨4009367304271739900643785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672911536181159933762523 4009367304271739900643785)
            ·
              refine ⟨3007025478203804925482839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4009367304271739900643785 3007025478203804925482839)
              ·
                refine ⟨4510538217305707388224259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007025478203804925482839 4510538217305707388224259)
                ·
                  refine ⟨6765807325958561082336389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510538217305707388224259 6765807325958561082336389)
                  ·
                    refine ⟨1268588873617230202938073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6765807325958561082336389 1268588873617230202938073)
                    ·
                      refine ⟨951441655212922652203555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268588873617230202938073 951441655212922652203555)
                      ·
                        rfl

theorem cell23_1852926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1852926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852926 prefixEnd_1852926 := by exact prefixLift 1852926
  have htrace : WordTrace (prefixWord ++ tailWord_1852926) baseStart_1852926 baseEnd_1852926 := by
    simpa [prefixWord, tailWord_1852926, baseEnd_1852926] using wordTrace_append hprefix tailTrace_1852926
  have hstable : (prefixWord ++ tailWord_1852926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852926).length < 2 ^ (prefixWord ++ tailWord_1852926).sum := by decide
  have hdescent : baseEnd_1852926 < baseStart_1852926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852978 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1852978 : Nat := 118140960795 + 1852978 * 2 ^ 59
def prefixEnd_1852978 : Nat := 4983230072969 + 3 ^ 40 * 1852978 * 2
def baseEnd_1852978 : Nat := 951468356206956448753315

theorem tailTrace_1852978 : CollatzResearch.WordTrace tailWord_1852978 prefixEnd_1852978 951468356206956448753315 := by
  unfold tailWord_1852978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895914970246161073141897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45055773253989762861711725 16895914970246161073141897)
  ·
    refine ⟨12671936227684620804856423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16895914970246161073141897 12671936227684620804856423)
    ·
      refine ⟨19007904341526931207284635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671936227684620804856423 19007904341526931207284635)
      ·
        refine ⟨28511856512290396810926953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19007904341526931207284635 28511856512290396810926953)
        ·
          refine ⟨21383892384217797608195215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28511856512290396810926953 21383892384217797608195215)
          ·
            refine ⟨32075838576326696412292823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21383892384217797608195215 32075838576326696412292823)
            ·
              refine ⟨48113757864490044618439235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32075838576326696412292823 48113757864490044618439235)
              ·
                refine ⟨72170636796735066927658853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48113757864490044618439235 72170636796735066927658853)
                ·
                  refine ⟨13531994399387825048936035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72170636796735066927658853 13531994399387825048936035)
                  ·
                    refine ⟨20297991599081737573404053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13531994399387825048936035 20297991599081737573404053)
                    ·
                      refine ⟨951468356206956448753315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20297991599081737573404053 951468356206956448753315)
                      ·
                        rfl

theorem cell23_1852978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1852978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852978 prefixEnd_1852978 := by exact prefixLift 1852978
  have htrace : WordTrace (prefixWord ++ tailWord_1852978) baseStart_1852978 baseEnd_1852978 := by
    simpa [prefixWord, tailWord_1852978, baseEnd_1852978] using wordTrace_append hprefix tailTrace_1852978
  have hstable : (prefixWord ++ tailWord_1852978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852978).length < 2 ^ (prefixWord ++ tailWord_1852978).sum := by decide
  have hdescent : baseEnd_1852978 < baseStart_1852978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852985 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1852985 : Nat := 118140960795 + 1852985 * 2 ^ 59
def prefixEnd_1852985 : Nat := 4983230072969 + 3 ^ 40 * 1852985 * 2
def baseEnd_1852985 : Nat := 951471950571537921365783

theorem tailTrace_1852985 : CollatzResearch.WordTrace tailWord_1852985 prefixEnd_1852985 951471950571537921365783 := by
  unfold tailWord_1852985
  simp only [CollatzResearch.WordTrace]
  refine ⟨67583915191959284488072409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45055943461306189658714939 67583915191959284488072409)
  ·
    refine ⟨50687936393969463366054307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67583915191959284488072409 50687936393969463366054307)
    ·
      refine ⟨76031904590954195049081461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50687936393969463366054307 76031904590954195049081461)
      ·
        refine ⟨7127991055401955785851387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76031904590954195049081461 7127991055401955785851387)
        ·
          refine ⟨10691986583102933678777081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127991055401955785851387 10691986583102933678777081)
          ·
            refine ⟨8018989937327200259082811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10691986583102933678777081 8018989937327200259082811)
            ·
              refine ⟨12028484905990800388624217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018989937327200259082811 12028484905990800388624217)
              ·
                refine ⟨9021363679493100291468163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12028484905990800388624217 9021363679493100291468163)
                ·
                  refine ⟨13532045519239650437202245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9021363679493100291468163 13532045519239650437202245)
                  ·
                    refine ⟨2537258534857434456975421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13532045519239650437202245 2537258534857434456975421)
                    ·
                      refine ⟨951471950571537921365783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537258534857434456975421 951471950571537921365783)
                      ·
                        rfl

theorem cell23_1852985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1852985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1852985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1852985 prefixEnd_1852985 := by exact prefixLift 1852985
  have htrace : WordTrace (prefixWord ++ tailWord_1852985) baseStart_1852985 baseEnd_1852985 := by
    simpa [prefixWord, tailWord_1852985, baseEnd_1852985] using wordTrace_append hprefix tailTrace_1852985
  have hstable : (prefixWord ++ tailWord_1852985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852985).length < 2 ^ (prefixWord ++ tailWord_1852985).sum := by decide
  have hdescent : baseEnd_1852985 < baseStart_1852985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853065 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 6, 4]
def baseStart_1853065 : Nat := 118140960795 + 1853065 * 2 ^ 59
def prefixEnd_1853065 : Nat := 4983230072969 + 3 ^ 40 * 1853065 * 2
def baseEnd_1853065 : Nat := 317171009674632536121805

theorem tailTrace_1853065 : CollatzResearch.WordTrace tailWord_1853065 prefixEnd_1853065 317171009674632536121805 := by
  unfold tailWord_1853065
  simp only [CollatzResearch.WordTrace]
  refine ⟨67586833031669458150984649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45057888687779638767323099 67586833031669458150984649)
  ·
    refine ⟨50690124773752093613238487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67586833031669458150984649 50690124773752093613238487)
    ·
      refine ⟨76035187160628140419857731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50690124773752093613238487 76035187160628140419857731)
      ·
        refine ⟨114052780740942210629786597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76035187160628140419857731 114052780740942210629786597)
        ·
          refine ⟨21384896388926664493084987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114052780740942210629786597 21384896388926664493084987)
          ·
            refine ⟨32077344583389996739627481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21384896388926664493084987 32077344583389996739627481)
            ·
              refine ⟨24058008437542497554720611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32077344583389996739627481 24058008437542497554720611)
              ·
                refine ⟨36087012656313746332080917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24058008437542497554720611 36087012656313746332080917)
                ·
                  refine ⟨1691578718264706859316293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36087012656313746332080917 1691578718264706859316293)
                  ·
                    refine ⟨317171009674632536121805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1691578718264706859316293 317171009674632536121805)
                    ·
                      rfl

theorem cell23_1853065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_1853065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853065 prefixEnd_1853065 := by exact prefixLift 1853065
  have htrace : WordTrace (prefixWord ++ tailWord_1853065) baseStart_1853065 baseEnd_1853065 := by
    simpa [prefixWord, tailWord_1853065, baseEnd_1853065] using wordTrace_append hprefix tailTrace_1853065
  have hstable : (prefixWord ++ tailWord_1853065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853065).length < 2 ^ (prefixWord ++ tailWord_1853065).sum := by decide
  have hdescent : baseEnd_1853065 < baseStart_1853065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853075 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 3]
def baseStart_1853075 : Nat := 118140960795 + 1853075 * 2 ^ 59
def prefixEnd_1853075 : Nat := 4983230072969 + 3 ^ 40 * 1853075 * 2
def baseEnd_1853075 : Nat := 951518163830442569240369

theorem tailTrace_1853075 : CollatzResearch.WordTrace tailWord_1853075 prefixEnd_1853075 951518163830442569240369 := by
  unfold tailWord_1853075
  simp only [CollatzResearch.WordTrace]
  refine ⟨67587197761633229858848679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45058131841088819905899119 67587197761633229858848679)
  ·
    refine ⟨101380796642449844788273019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67587197761633229858848679 101380796642449844788273019)
    ·
      refine ⟨152071194963674767182409529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101380796642449844788273019 152071194963674767182409529)
      ·
        refine ⟨114053396222756075386807147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152071194963674767182409529 114053396222756075386807147)
        ·
          refine ⟨171080094334134113080210721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114053396222756075386807147 171080094334134113080210721)
          ·
            refine ⟨128310070750600584810158041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171080094334134113080210721 128310070750600584810158041)
            ·
              refine ⟨96232553062950438607618531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128310070750600584810158041 96232553062950438607618531)
              ·
                refine ⟨144348829594425657911427797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96232553062950438607618531 144348829594425657911427797)
                ·
                  refine ⟨3383175693619351357299089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 144348829594425657911427797 3383175693619351357299089)
                  ·
                    refine ⟨2537381770214513517974317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3383175693619351357299089 2537381770214513517974317)
                    ·
                      refine ⟨951518163830442569240369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537381770214513517974317 951518163830442569240369)
                      ·
                        rfl

theorem cell23_1853075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_1853075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853075 prefixEnd_1853075 := by exact prefixLift 1853075
  have htrace : WordTrace (prefixWord ++ tailWord_1853075) baseStart_1853075 baseEnd_1853075 := by
    simpa [prefixWord, tailWord_1853075, baseEnd_1853075] using wordTrace_append hprefix tailTrace_1853075
  have hstable : (prefixWord ++ tailWord_1853075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853075).length < 2 ^ (prefixWord ++ tailWord_1853075).sum := by decide
  have hdescent : baseEnd_1853075 < baseStart_1853075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853085 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1853085 : Nat := 118140960795 + 1853085 * 2 ^ 59
def prefixEnd_1853085 : Nat := 4983230072969 + 3 ^ 40 * 1853085 * 2
def baseEnd_1853085 : Nat := 951523298636987530115323

theorem tailTrace_1853085 : CollatzResearch.WordTrace tailWord_1853085 prefixEnd_1853085 951523298636987530115323 := by
  unfold tailWord_1853085
  simp only [CollatzResearch.WordTrace]
  refine ⟨67587562491597001566712709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45058374994398001044475139 67587562491597001566712709)
  ·
    refine ⟨12672667967174437793758633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67587562491597001566712709 12672667967174437793758633)
    ·
      refine ⟨9504500975380828345318975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12672667967174437793758633 9504500975380828345318975)
      ·
        refine ⟨14256751463071242517978463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9504500975380828345318975 14256751463071242517978463)
        ·
          refine ⟨21385127194606863776967695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14256751463071242517978463 21385127194606863776967695)
          ·
            refine ⟨32077690791910295665451543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21385127194606863776967695 32077690791910295665451543)
            ·
              refine ⟨48116536187865443498177315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32077690791910295665451543 48116536187865443498177315)
              ·
                refine ⟨72174804281798165247265973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48116536187865443498177315 72174804281798165247265973)
                ·
                  refine ⟨6766387901418577991931185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72174804281798165247265973 6766387901418577991931185)
                  ·
                    refine ⟨5074790926063933493948389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766387901418577991931185 5074790926063933493948389)
                    ·
                      refine ⟨951523298636987530115323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5074790926063933493948389 951523298636987530115323)
                      ·
                        rfl

theorem cell23_1853085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1853085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853085 prefixEnd_1853085 := by exact prefixLift 1853085
  have htrace : WordTrace (prefixWord ++ tailWord_1853085) baseStart_1853085 baseEnd_1853085 := by
    simpa [prefixWord, tailWord_1853085, baseEnd_1853085] using wordTrace_append hprefix tailTrace_1853085
  have hstable : (prefixWord ++ tailWord_1853085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853085).length < 2 ^ (prefixWord ++ tailWord_1853085).sum := by decide
  have hdescent : baseEnd_1853085 < baseStart_1853085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853092 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_1853092 : Nat := 118140960795 + 1853092 * 2 ^ 59
def prefixEnd_1853092 : Nat := 4983230072969 + 3 ^ 40 * 1853092 * 2
def baseEnd_1853092 : Nat := 951526893001569002727791

theorem tailTrace_1853092 : CollatzResearch.WordTrace tailWord_1853092 prefixEnd_1853092 951526893001569002727791 := by
  unfold tailWord_1853092
  simp only [CollatzResearch.WordTrace]
  refine ⟨33793908901285820881108765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45058545201714427841478353 33793908901285820881108765)
  ·
    refine ⟨12672715837982182830415787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33793908901285820881108765 12672715837982182830415787)
    ·
      refine ⟨19009073756973274245623681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12672715837982182830415787 19009073756973274245623681)
      ·
        refine ⟨14256805317729955684217761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19009073756973274245623681 14256805317729955684217761)
        ·
          refine ⟨10692603988297466763163321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14256805317729955684217761 10692603988297466763163321)
          ·
            refine ⟨8019452991223100072372491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692603988297466763163321 8019452991223100072372491)
            ·
              refine ⟨12029179486834650108558737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8019452991223100072372491 12029179486834650108558737)
              ·
                refine ⟨9021884615125987581419053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12029179486834650108558737 9021884615125987581419053)
                ·
                  refine ⟨3383206730672245343032145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9021884615125987581419053 3383206730672245343032145)
                  ·
                    refine ⟨2537405048004184007274109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3383206730672245343032145 2537405048004184007274109)
                    ·
                      refine ⟨951526893001569002727791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537405048004184007274109 951526893001569002727791)
                      ·
                        rfl

theorem cell23_1853092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_1853092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853092 prefixEnd_1853092 := by exact prefixLift 1853092
  have htrace : WordTrace (prefixWord ++ tailWord_1853092) baseStart_1853092 baseEnd_1853092 := by
    simpa [prefixWord, tailWord_1853092, baseEnd_1853092] using wordTrace_append hprefix tailTrace_1853092
  have hstable : (prefixWord ++ tailWord_1853092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853092).length < 2 ^ (prefixWord ++ tailWord_1853092).sum := by decide
  have hdescent : baseEnd_1853092 < baseStart_1853092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853133 : List Nat := [1, 6, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1853133 : Nat := 118140960795 + 1853133 * 2 ^ 59
def prefixEnd_1853133 : Nat := 4983230072969 + 3 ^ 40 * 1853133 * 2
def baseEnd_1853133 : Nat := 317182648569467780771701

theorem tailTrace_1853133 : CollatzResearch.WordTrace tailWord_1853133 prefixEnd_1853133 317182648569467780771701 := by
  unfold tailWord_1853133
  simp only [CollatzResearch.WordTrace]
  refine ⟨67589313195423105764460053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45059542130282070509640035 67589313195423105764460053)
  ·
    refine ⟨3168249056035458082709065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67589313195423105764460053 3168249056035458082709065)
    ·
      refine ⟨2376186792026593562031799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3168249056035458082709065 2376186792026593562031799)
      ·
        refine ⟨3564280188039890343047699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376186792026593562031799 3564280188039890343047699)
        ·
          refine ⟨5346420282059835514571549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564280188039890343047699 5346420282059835514571549)
          ·
            refine ⟨2004907605772438317964331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5346420282059835514571549 2004907605772438317964331)
            ·
              refine ⟨3007361408658657476946497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004907605772438317964331 3007361408658657476946497)
              ·
                refine ⟨2255521056493993107709873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3007361408658657476946497 2255521056493993107709873)
                ·
                  refine ⟨1691640792370494830782405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2255521056493993107709873 1691640792370494830782405)
                  ·
                    refine ⟨317182648569467780771701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1691640792370494830782405 317182648569467780771701)
                    ·
                      rfl

theorem cell23_1853133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1853133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853133 prefixEnd_1853133 := by exact prefixLift 1853133
  have htrace : WordTrace (prefixWord ++ tailWord_1853133) baseStart_1853133 baseEnd_1853133 := by
    simpa [prefixWord, tailWord_1853133, baseEnd_1853133] using wordTrace_append hprefix tailTrace_1853133
  have hstable : (prefixWord ++ tailWord_1853133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853133).length < 2 ^ (prefixWord ++ tailWord_1853133).sum := by decide
  have hdescent : baseEnd_1853133 < baseStart_1853133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853156 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_1853156 : Nat := 118140960795 + 1853156 * 2 ^ 59
def prefixEnd_1853156 : Nat := 4983230072969 + 3 ^ 40 * 1853156 * 2
def baseEnd_1853156 : Nat := 951559755763456752327497

theorem tailTrace_1853156 : CollatzResearch.WordTrace tailWord_1853156 prefixEnd_1853156 951559755763456752327497 := by
  unfold tailWord_1853156
  simp only [CollatzResearch.WordTrace]
  refine ⟨33795076037169890346273661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45060101382893187128364881 33795076037169890346273661)
  ·
    refine ⟨12673153513938708879852623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33795076037169890346273661 12673153513938708879852623)
    ·
      refine ⟨19009730270908063319778935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12673153513938708879852623 19009730270908063319778935)
      ·
        refine ⟨28514595406362094979668403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19009730270908063319778935 28514595406362094979668403)
        ·
          refine ⟨42771893109543142469502605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28514595406362094979668403 42771893109543142469502605)
          ·
            refine ⟨16039459916078678426063477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42771893109543142469502605 16039459916078678426063477)
            ·
              refine ⟨1503699367132376102443451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16039459916078678426063477 1503699367132376102443451)
              ·
                refine ⟨2255549050698564153665177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503699367132376102443451 2255549050698564153665177)
                ·
                  refine ⟨1691661788023923115248883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2255549050698564153665177 1691661788023923115248883)
                  ·
                    refine ⟨2537492682035884672873325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1691661788023923115248883 2537492682035884672873325)
                    ·
                      refine ⟨951559755763456752327497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537492682035884672873325 951559755763456752327497)
                      ·
                        rfl

theorem cell23_1853156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_1853156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853156 prefixEnd_1853156 := by exact prefixLift 1853156
  have htrace : WordTrace (prefixWord ++ tailWord_1853156) baseStart_1853156 baseEnd_1853156 := by
    simpa [prefixWord, tailWord_1853156, baseEnd_1853156] using wordTrace_append hprefix tailTrace_1853156
  have hstable : (prefixWord ++ tailWord_1853156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853156).length < 2 ^ (prefixWord ++ tailWord_1853156).sum := by decide
  have hdescent : baseEnd_1853156 < baseStart_1853156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853166 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_1853166 : Nat := 118140960795 + 1853166 * 2 ^ 59
def prefixEnd_1853166 : Nat := 4983230072969 + 3 ^ 40 * 1853166 * 2
def baseEnd_1853166 : Nat := 951564890570001713202451

theorem tailTrace_1853166 : CollatzResearch.WordTrace tailWord_1853166 prefixEnd_1853166 951564890570001713202451 := by
  unfold tailWord_1853166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8448814600537944050051419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45060344536202368266940901 8448814600537944050051419)
  ·
    refine ⟨12673221900806916075077129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8448814600537944050051419 12673221900806916075077129)
    ·
      refine ⟨9504916425605187056307847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12673221900806916075077129 9504916425605187056307847)
      ·
        refine ⟨14257374638407780584461771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9504916425605187056307847 14257374638407780584461771)
        ·
          refine ⟨21386061957611670876692657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14257374638407780584461771 21386061957611670876692657)
          ·
            refine ⟨16039546468208753157519493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21386061957611670876692657 16039546468208753157519493)
            ·
              refine ⟨3007414962789141217034905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16039546468208753157519493 3007414962789141217034905)
              ·
                refine ⟨2255561222091855912776179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3007414962789141217034905 2255561222091855912776179)
                ·
                  refine ⟨3383341833137783869164269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255561222091855912776179 3383341833137783869164269)
                  ·
                    refine ⟨1268753187426668950936601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383341833137783869164269 1268753187426668950936601)
                    ·
                      refine ⟨951564890570001713202451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268753187426668950936601 951564890570001713202451)
                      ·
                        rfl

theorem cell23_1853166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_1853166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853166 prefixEnd_1853166 := by exact prefixLift 1853166
  have htrace : WordTrace (prefixWord ++ tailWord_1853166) baseStart_1853166 baseEnd_1853166 := by
    simpa [prefixWord, tailWord_1853166, baseEnd_1853166] using wordTrace_append hprefix tailTrace_1853166
  have hstable : (prefixWord ++ tailWord_1853166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853166).length < 2 ^ (prefixWord ++ tailWord_1853166).sum := by decide
  have hdescent : baseEnd_1853166 < baseStart_1853166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853175 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1853175 : Nat := 118140960795 + 1853175 * 2 ^ 59
def prefixEnd_1853175 : Nat := 4983230072969 + 3 ^ 40 * 1853175 * 2
def baseEnd_1853175 : Nat := 951569511895892177989909

theorem tailTrace_1853175 : CollatzResearch.WordTrace tailWord_1853175 prefixEnd_1853175 951569511895892177989909 := by
  unfold tailWord_1853175
  simp only [CollatzResearch.WordTrace]
  refine ⟨67590845061270946937488979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45060563374180631291659319 67590845061270946937488979)
  ·
    refine ⟨101386267591906420406233469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67590845061270946937488979 101386267591906420406233469)
    ·
      refine ⟨38019850346964907652337551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101386267591906420406233469 38019850346964907652337551)
      ·
        refine ⟨57029775520447361478506327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38019850346964907652337551 57029775520447361478506327)
        ·
          refine ⟨85544663280671042217759491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57029775520447361478506327 85544663280671042217759491)
          ·
            refine ⟨128316994921006563326639237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85544663280671042217759491 128316994921006563326639237)
            ·
              refine ⟨24059436547688730623744857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128316994921006563326639237 24059436547688730623744857)
              ·
                refine ⟨18044577410766547967808643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24059436547688730623744857 18044577410766547967808643)
                ·
                  refine ⟨27066866116149821951712965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18044577410766547967808643 27066866116149821951712965)
                  ·
                    refine ⟨5075037396778091615946181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27066866116149821951712965 5075037396778091615946181)
                    ·
                      refine ⟨951569511895892177989909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5075037396778091615946181 951569511895892177989909)
                      ·
                        rfl

theorem cell23_1853175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1853175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853175 prefixEnd_1853175 := by exact prefixLift 1853175
  have htrace : WordTrace (prefixWord ++ tailWord_1853175) baseStart_1853175 baseEnd_1853175 := by
    simpa [prefixWord, tailWord_1853175, baseEnd_1853175] using wordTrace_append hprefix tailTrace_1853175
  have hstable : (prefixWord ++ tailWord_1853175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853175).length < 2 ^ (prefixWord ++ tailWord_1853175).sum := by decide
  have hdescent : baseEnd_1853175 < baseStart_1853175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853185 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 9]
def baseStart_1853185 : Nat := 118140960795 + 1853185 * 2 ^ 59
def prefixEnd_1853185 : Nat := 4983230072969 + 3 ^ 40 * 1853185 * 2
def baseEnd_1853185 : Nat := 105730516300270793207207

theorem tailTrace_1853185 : CollatzResearch.WordTrace tailWord_1853185 prefixEnd_1853185 105730516300270793207207 := by
  unfold tailWord_1853185
  simp only [CollatzResearch.WordTrace]
  refine ⟨67591209791234718645353009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45060806527489812430235339 67591209791234718645353009)
  ·
    refine ⟨50693407343426038984014757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67591209791234718645353009 50693407343426038984014757)
    ·
      refine ⟨9505013876892382309502767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50693407343426038984014757 9505013876892382309502767)
      ·
        refine ⟨14257520815338573464254151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9505013876892382309502767 14257520815338573464254151)
        ·
          refine ⟨21386281223007860196381227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14257520815338573464254151 21386281223007860196381227)
          ·
            refine ⟨32079421834511790294571841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21386281223007860196381227 32079421834511790294571841)
            ·
              refine ⟨24059566375883842720928881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32079421834511790294571841 24059566375883842720928881)
              ·
                refine ⟨18044674781912882040696661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24059566375883842720928881 18044674781912882040696661)
                ·
                  refine ⟨105730516300270793207207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18044674781912882040696661 105730516300270793207207)
                  ·
                    rfl

theorem cell23_1853185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 9].length) (baseStart_1853185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853185 prefixEnd_1853185 := by exact prefixLift 1853185
  have htrace : WordTrace (prefixWord ++ tailWord_1853185) baseStart_1853185 baseEnd_1853185 := by
    simpa [prefixWord, tailWord_1853185, baseEnd_1853185] using wordTrace_append hprefix tailTrace_1853185
  have hstable : (prefixWord ++ tailWord_1853185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853185).length < 2 ^ (prefixWord ++ tailWord_1853185).sum := by decide
  have hdescent : baseEnd_1853185 < baseStart_1853185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853212 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1853212 : Nat := 118140960795 + 1853212 * 2 ^ 59
def prefixEnd_1853212 : Nat := 4983230072969 + 3 ^ 40 * 1853212 * 2
def baseEnd_1853212 : Nat := 951588510680108533227239

theorem tailTrace_1853212 : CollatzResearch.WordTrace tailWord_1853212 prefixEnd_1853212 951588510680108533227239 := by
  unfold tailWord_1853212
  simp only [CollatzResearch.WordTrace]
  refine ⟨33796097281068451128292945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45061463041424601504390593 33796097281068451128292945)
  ·
    refine ⟨25347072960801338346219709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33796097281068451128292945 25347072960801338346219709)
    ·
      refine ⟨9505152360300501879832391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25347072960801338346219709 9505152360300501879832391)
      ·
        refine ⟨14257728540450752819748587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9505152360300501879832391 14257728540450752819748587)
        ·
          refine ⟨21386592810676129229622881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14257728540450752819748587 21386592810676129229622881)
          ·
            refine ⟨16039944608007096922217161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21386592810676129229622881 16039944608007096922217161)
            ·
              refine ⟨12029958456005322691662871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16039944608007096922217161 12029958456005322691662871)
              ·
                refine ⟨18044937684007984037494307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12029958456005322691662871 18044937684007984037494307)
                ·
                  refine ⟨27067406526011976056241461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18044937684007984037494307 27067406526011976056241461)
                  ·
                    refine ⟨2537569361813622755272637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27067406526011976056241461 2537569361813622755272637)
                    ·
                      refine ⟨951588510680108533227239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537569361813622755272637 951588510680108533227239)
                      ·
                        rfl

theorem cell23_1853212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1853212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853212 prefixEnd_1853212 := by exact prefixLift 1853212
  have htrace : WordTrace (prefixWord ++ tailWord_1853212) baseStart_1853212 baseEnd_1853212 := by
    simpa [prefixWord, tailWord_1853212, baseEnd_1853212] using wordTrace_append hprefix tailTrace_1853212
  have hstable : (prefixWord ++ tailWord_1853212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853212).length < 2 ^ (prefixWord ++ tailWord_1853212).sum := by decide
  have hdescent : baseEnd_1853212 < baseStart_1853212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853225 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_1853225 : Nat := 118140960795 + 1853225 * 2 ^ 59
def prefixEnd_1853225 : Nat := 4983230072969 + 3 ^ 40 * 1853225 * 2
def baseEnd_1853225 : Nat := 951595185928616982364679

theorem tailTrace_1853225 : CollatzResearch.WordTrace tailWord_1853225 prefixEnd_1853225 951595185928616982364679 := by
  unfold tailWord_1853225
  simp only [CollatzResearch.WordTrace]
  refine ⟨67592668711089805476809129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45061779140726536984539419 67592668711089805476809129)
  ·
    refine ⟨50694501533317354107606847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67592668711089805476809129 50694501533317354107606847)
    ·
      refine ⟨76041752299976031161410271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50694501533317354107606847 76041752299976031161410271)
      ·
        refine ⟨114062628449964046742115407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76041752299976031161410271 114062628449964046742115407)
        ·
          refine ⟨171093942674946070113173111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114062628449964046742115407 171093942674946070113173111)
          ·
            refine ⟨256640914012419105169759667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171093942674946070113173111 256640914012419105169759667)
            ·
              refine ⟨384961371018628657754639501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256640914012419105169759667 384961371018628657754639501)
              ·
                refine ⟨144360514131985746657989813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384961371018628657754639501 144360514131985746657989813)
                ·
                  refine ⟨13533798199873663749186545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144360514131985746657989813 13533798199873663749186545)
                  ·
                    refine ⟨10150348649905247811889909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13533798199873663749186545 10150348649905247811889909)
                    ·
                      refine ⟨951595185928616982364679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10150348649905247811889909 951595185928616982364679)
                      ·
                        rfl

theorem cell23_1853225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_1853225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853225 prefixEnd_1853225 := by exact prefixLift 1853225
  have htrace : WordTrace (prefixWord ++ tailWord_1853225) baseStart_1853225 baseEnd_1853225 := by
    simpa [prefixWord, tailWord_1853225, baseEnd_1853225] using wordTrace_append hprefix tailTrace_1853225
  have hstable : (prefixWord ++ tailWord_1853225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853225).length < 2 ^ (prefixWord ++ tailWord_1853225).sum := by decide
  have hdescent : baseEnd_1853225 < baseStart_1853225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853242 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_1853242 : Nat := 118140960795 + 1853242 * 2 ^ 59
def prefixEnd_1853242 : Nat := 4983230072969 + 3 ^ 40 * 1853242 * 2
def baseEnd_1853242 : Nat := 951603915099743415852101

theorem tailTrace_1853242 : CollatzResearch.WordTrace tailWord_1853242 prefixEnd_1853242 951603915099743415852101 := by
  unfold tailWord_1853242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16898322188007054345044495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45062192501352144920118653 16898322188007054345044495)
  ·
    refine ⟨25347483282010581517566743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16898322188007054345044495 25347483282010581517566743)
    ·
      refine ⟨38021224923015872276350115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25347483282010581517566743 38021224923015872276350115)
      ·
        refine ⟨57031837384523808414525173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38021224923015872276350115 57031837384523808414525173)
        ·
          refine ⟨5346734754799107038861735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57031837384523808414525173 5346734754799107038861735)
          ·
            refine ⟨8020102132198660558292603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346734754799107038861735 8020102132198660558292603)
            ·
              refine ⟨12030153198297990837438905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020102132198660558292603 12030153198297990837438905)
              ·
                refine ⟨9022614898723493128079179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12030153198297990837438905 9022614898723493128079179)
                ·
                  refine ⟨13533922348085239692118769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9022614898723493128079179 13533922348085239692118769)
                  ·
                    refine ⟨10150441761063929769089077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13533922348085239692118769 10150441761063929769089077)
                    ·
                      refine ⟨951603915099743415852101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10150441761063929769089077 951603915099743415852101)
                      ·
                        rfl

theorem cell23_1853242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_1853242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853242 prefixEnd_1853242 := by exact prefixLift 1853242
  have htrace : WordTrace (prefixWord ++ tailWord_1853242) baseStart_1853242 baseEnd_1853242 := by
    simpa [prefixWord, tailWord_1853242, baseEnd_1853242] using wordTrace_append hprefix tailTrace_1853242
  have hstable : (prefixWord ++ tailWord_1853242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853242).length < 2 ^ (prefixWord ++ tailWord_1853242).sum := by decide
  have hdescent : baseEnd_1853242 < baseStart_1853242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853269 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_1853269 : Nat := 118140960795 + 1853269 * 2 ^ 59
def prefixEnd_1853269 : Nat := 4983230072969 + 3 ^ 40 * 1853269 * 2
def baseEnd_1853269 : Nat := 951617779077414810214477

theorem tailTrace_1853269 : CollatzResearch.WordTrace tailWord_1853269 prefixEnd_1853269 951617779077414810214477 := by
  unfold tailWord_1853269
  simp only [CollatzResearch.WordTrace]
  refine ⟨67594273522930400991410861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45062849015286933994273907 67594273522930400991410861)
  ·
    refine ⟨25347852571098900371779073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67594273522930400991410861 25347852571098900371779073)
    ·
      refine ⟨19010889428324175278834305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25347852571098900371779073 19010889428324175278834305)
      ·
        refine ⟨14258167071243131459125729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19010889428324175278834305 14258167071243131459125729)
        ·
          refine ⟨10693625303432348594344297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14258167071243131459125729 10693625303432348594344297)
          ·
            refine ⟨8020218977574261445758223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10693625303432348594344297 8020218977574261445758223)
            ·
              refine ⟨12030328466361392168637335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8020218977574261445758223 12030328466361392168637335)
              ·
                refine ⟨18045492699542088252956003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12030328466361392168637335 18045492699542088252956003)
                ·
                  refine ⟨27068239049313132379434005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18045492699542088252956003 27068239049313132379434005)
                  ·
                    refine ⟨1268823705436553080285969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27068239049313132379434005 1268823705436553080285969)
                    ·
                      refine ⟨951617779077414810214477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268823705436553080285969 951617779077414810214477)
                      ·
                        rfl

theorem cell23_1853269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_1853269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853269 prefixEnd_1853269 := by exact prefixLift 1853269
  have htrace : WordTrace (prefixWord ++ tailWord_1853269) baseStart_1853269 baseEnd_1853269 := by
    simpa [prefixWord, tailWord_1853269, baseEnd_1853269] using wordTrace_append hprefix tailTrace_1853269
  have hstable : (prefixWord ++ tailWord_1853269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853269).length < 2 ^ (prefixWord ++ tailWord_1853269).sum := by decide
  have hdescent : baseEnd_1853269 < baseStart_1853269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853279 : List Nat := [1, 1, 2, 3, 1, 5, 1, 2, 3, 4]
def baseStart_1853279 : Nat := 118140960795 + 1853279 * 2 ^ 59
def prefixEnd_1853279 : Nat := 4983230072969 + 3 ^ 40 * 1853279 * 2
def baseEnd_1853279 : Nat := 317207637961319923696477

theorem tailTrace_1853279 : CollatzResearch.WordTrace tailWord_1853279 prefixEnd_1853279 317207637961319923696477 := by
  unfold tailWord_1853279
  simp only [CollatzResearch.WordTrace]
  refine ⟨67594638252894172699274891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45063092168596115132849927 67594638252894172699274891)
  ·
    refine ⟨101391957379341259048912337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67594638252894172699274891 101391957379341259048912337)
    ·
      refine ⟨76043968034505944286684253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101391957379341259048912337 76043968034505944286684253)
      ·
        refine ⟨28516488012939729107506595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76043968034505944286684253 28516488012939729107506595)
        ·
          refine ⟨42774732019409593661259893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28516488012939729107506595 42774732019409593661259893)
          ·
            refine ⟨4010131126819649405743115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42774732019409593661259893 4010131126819649405743115)
            ·
              refine ⟨6015196690229474108614673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010131126819649405743115 6015196690229474108614673)
              ·
                refine ⟨4511397517672105581461005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6015196690229474108614673 4511397517672105581461005)
                ·
                  refine ⟨1691774069127039593047877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4511397517672105581461005 1691774069127039593047877)
                  ·
                    refine ⟨317207637961319923696477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1691774069127039593047877 317207637961319923696477)
                    ·
                      rfl

theorem cell23_1853279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 4].length) (baseStart_1853279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853279 prefixEnd_1853279 := by exact prefixLift 1853279
  have htrace : WordTrace (prefixWord ++ tailWord_1853279) baseStart_1853279 baseEnd_1853279 := by
    simpa [prefixWord, tailWord_1853279, baseEnd_1853279] using wordTrace_append hprefix tailTrace_1853279
  have hstable : (prefixWord ++ tailWord_1853279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853279).length < 2 ^ (prefixWord ++ tailWord_1853279).sum := by decide
  have hdescent : baseEnd_1853279 < baseStart_1853279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853313 : List Nat := [1, 2, 4, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1853313 : Nat := 118140960795 + 1853313 * 2 ^ 59
def prefixEnd_1853313 : Nat := 4983230072969 + 3 ^ 40 * 1853313 * 2
def baseEnd_1853313 : Nat := 317213457408737546021425

theorem tailTrace_1853313 : CollatzResearch.WordTrace tailWord_1853313 prefixEnd_1853313 317213457408737546021425 := by
  unfold tailWord_1853313
  simp only [CollatzResearch.WordTrace]
  refine ⟨67595878334770996506012593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45063918889847331004008395 67595878334770996506012593)
  ·
    refine ⟨50696908751078247379509445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67595878334770996506012593 50696908751078247379509445)
    ·
      refine ⟨9505670390827171383658021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50696908751078247379509445 9505670390827171383658021)
      ·
        refine ⟨1782313198280094634435879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9505670390827171383658021 1782313198280094634435879)
        ·
          refine ⟨2673469797420141951653819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782313198280094634435879 2673469797420141951653819)
          ·
            refine ⟨4010204696130212927480729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673469797420141951653819 4010204696130212927480729)
            ·
              refine ⟨3007653522097659695610547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4010204696130212927480729 3007653522097659695610547)
              ·
                refine ⟨4511480283146489543415821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007653522097659695610547 4511480283146489543415821)
                ·
                  refine ⟨1691805106179933578780933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4511480283146489543415821 1691805106179933578780933)
                  ·
                    refine ⟨317213457408737546021425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1691805106179933578780933 317213457408737546021425)
                    ·
                      rfl

theorem cell23_1853313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1853313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853313 prefixEnd_1853313 := by exact prefixLift 1853313
  have htrace : WordTrace (prefixWord ++ tailWord_1853313) baseStart_1853313 baseEnd_1853313 := by
    simpa [prefixWord, tailWord_1853313, baseEnd_1853313] using wordTrace_append hprefix tailTrace_1853313
  have hstable : (prefixWord ++ tailWord_1853313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853313).length < 2 ^ (prefixWord ++ tailWord_1853313).sum := by decide
  have hdescent : baseEnd_1853313 < baseStart_1853313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853329 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 1, 5, 2]
def baseStart_1853329 : Nat := 118140960795 + 1853329 * 2 ^ 59
def prefixEnd_1853329 : Nat := 4983230072969 + 3 ^ 40 * 1853329 * 2
def baseEnd_1853329 : Nat := 951648587916684575464201

theorem tailTrace_1853329 : CollatzResearch.WordTrace tailWord_1853329 prefixEnd_1853329 951648587916684575464201 := by
  unfold tailWord_1853329
  simp only [CollatzResearch.WordTrace]
  refine ⟨67596461902713031238595041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45064307935142020825730027 67596461902713031238595041)
  ·
    refine ⟨50697346427034773428946281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67596461902713031238595041 50697346427034773428946281)
    ·
      refine ⟨38023009820276080071709711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50697346427034773428946281 38023009820276080071709711)
      ·
        refine ⟨57034514730414120107564567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38023009820276080071709711 57034514730414120107564567)
        ·
          refine ⟨85551772095621180161346851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57034514730414120107564567 85551772095621180161346851)
          ·
            refine ⟨128327658143431770242020277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85551772095621180161346851 128327658143431770242020277)
            ·
              refine ⟨12030717950946728460189401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128327658143431770242020277 12030717950946728460189401)
              ·
                refine ⟨9023038463210046345142051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12030717950946728460189401 9023038463210046345142051)
                ·
                  refine ⟨13534557694815069517713077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9023038463210046345142051 13534557694815069517713077)
                  ·
                    refine ⟨1268864783888912767285601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13534557694815069517713077 1268864783888912767285601)
                    ·
                      refine ⟨951648587916684575464201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268864783888912767285601 951648587916684575464201)
                      ·
                        rfl

theorem cell23_1853329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_1853329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853329 prefixEnd_1853329 := by exact prefixLift 1853329
  have htrace : WordTrace (prefixWord ++ tailWord_1853329) baseStart_1853329 baseEnd_1853329 := by
    simpa [prefixWord, tailWord_1853329, baseEnd_1853329] using wordTrace_append hprefix tailTrace_1853329
  have hstable : (prefixWord ++ tailWord_1853329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853329).length < 2 ^ (prefixWord ++ tailWord_1853329).sum := by decide
  have hdescent : baseEnd_1853329 < baseStart_1853329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853359 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 4]
def baseStart_1853359 : Nat := 118140960795 + 1853359 * 2 ^ 59
def prefixEnd_1853359 : Nat := 4983230072969 + 3 ^ 40 * 1853359 * 2
def baseEnd_1853359 : Nat := 951663992336319458089063

theorem tailTrace_1853359 : CollatzResearch.WordTrace tailWord_1853359 prefixEnd_1853359 951663992336319458089063 := by
  unfold tailWord_1853359
  simp only [CollatzResearch.WordTrace]
  refine ⟨67597556092604346362187131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45065037395069564241458087 67597556092604346362187131)
  ·
    refine ⟨101396334138906519543280697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67597556092604346362187131 101396334138906519543280697)
    ·
      refine ⟨76047250604179889657460523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101396334138906519543280697 76047250604179889657460523)
      ·
        refine ⟨114070875906269834486190785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76047250604179889657460523 114070875906269834486190785)
        ·
          refine ⟨85553156929702375864643089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114070875906269834486190785 85553156929702375864643089)
          ·
            refine ⟨64164867697276781898482317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85553156929702375864643089 64164867697276781898482317)
            ·
              refine ⟨24061825386478793211930869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64164867697276781898482317 24061825386478793211930869)
              ·
                refine ⟨2255796129982386863618519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24061825386478793211930869 2255796129982386863618519)
                ·
                  refine ⟨3383694194973580295427779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255796129982386863618519 3383694194973580295427779)
                  ·
                    refine ⟨5075541292460370443141669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3383694194973580295427779 5075541292460370443141669)
                    ·
                      refine ⟨951663992336319458089063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5075541292460370443141669 951663992336319458089063)
                      ·
                        rfl

theorem cell23_1853359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_1853359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853359 prefixEnd_1853359 := by exact prefixLift 1853359
  have htrace : WordTrace (prefixWord ++ tailWord_1853359) baseStart_1853359 baseEnd_1853359 := by
    simpa [prefixWord, tailWord_1853359, baseEnd_1853359] using wordTrace_append hprefix tailTrace_1853359
  have hstable : (prefixWord ++ tailWord_1853359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853359).length < 2 ^ (prefixWord ++ tailWord_1853359).sum := by decide
  have hdescent : baseEnd_1853359 < baseStart_1853359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853369 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 4, 4]
def baseStart_1853369 : Nat := 118140960795 + 1853369 * 2 ^ 59
def prefixEnd_1853369 : Nat := 4983230072969 + 3 ^ 40 * 1853369 * 2
def baseEnd_1853369 : Nat := 317223042380954806321339

theorem tailTrace_1853369 : CollatzResearch.WordTrace tailWord_1853369 prefixEnd_1853369 317223042380954806321339 := by
  unfold tailWord_1853369
  simp only [CollatzResearch.WordTrace]
  refine ⟨67597920822568118070051161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45065280548378745380034107 67597920822568118070051161)
  ·
    refine ⟨50698440616926088552538371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67597920822568118070051161 50698440616926088552538371)
    ·
      refine ⟨76047660925389132828807557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50698440616926088552538371 76047660925389132828807557)
      ·
        refine ⟨14258936423510462405401417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76047660925389132828807557 14258936423510462405401417)
        ·
          refine ⟨10694202317632846804051063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14258936423510462405401417 10694202317632846804051063)
          ·
            refine ⟨16041303476449270206076595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694202317632846804051063 16041303476449270206076595)
            ·
              refine ⟨24061955214673905309114893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16041303476449270206076595 24061955214673905309114893)
              ·
                refine ⟨9023233205502714490918085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24061955214673905309114893 9023233205502714490918085)
                ·
                  refine ⟨1691856226031758967047141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9023233205502714490918085 1691856226031758967047141)
                  ·
                    refine ⟨317223042380954806321339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1691856226031758967047141 317223042380954806321339)
                    ·
                      rfl

theorem cell23_1853369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_1853369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853369 prefixEnd_1853369 := by exact prefixLift 1853369
  have htrace : WordTrace (prefixWord ++ tailWord_1853369) baseStart_1853369 baseEnd_1853369 := by
    simpa [prefixWord, tailWord_1853369, baseEnd_1853369] using wordTrace_append hprefix tailTrace_1853369
  have hstable : (prefixWord ++ tailWord_1853369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853369).length < 2 ^ (prefixWord ++ tailWord_1853369).sum := by decide
  have hdescent : baseEnd_1853369 < baseStart_1853369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853396 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1853396 : Nat := 118140960795 + 1853396 * 2 ^ 59
def prefixEnd_1853396 : Nat := 4983230072969 + 3 ^ 40 * 1853396 * 2
def baseEnd_1853396 : Nat := 951682991120535813326393

theorem tailTrace_1853396 : CollatzResearch.WordTrace tailWord_1853396 prefixEnd_1853396 951682991120535813326393 := by
  unfold tailWord_1853396
  simp only [CollatzResearch.WordTrace]
  refine ⟨33799452796735150840642021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45065937062313534454189361 33799452796735150840642021)
  ·
    refine ⟨6337397399387840782620379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33799452796735150840642021 6337397399387840782620379)
    ·
      refine ⟨9506096099081761173930569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337397399387840782620379 9506096099081761173930569)
      ·
        refine ⟨7129572074311320880447927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9506096099081761173930569 7129572074311320880447927)
        ·
          refine ⟨10694358111466981320671891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129572074311320880447927 10694358111466981320671891)
          ·
            refine ⟨16041537167200471981007837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694358111466981320671891 16041537167200471981007837)
            ·
              refine ⟨6015576437700176992877939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16041537167200471981007837 6015576437700176992877939)
              ·
                refine ⟨9023364656550265489316909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015576437700176992877939 9023364656550265489316909)
                ·
                  refine ⟨3383761746206349558493841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9023364656550265489316909 3383761746206349558493841)
                  ·
                    refine ⟨2537821309654762168870381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3383761746206349558493841 2537821309654762168870381)
                    ·
                      refine ⟨951682991120535813326393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537821309654762168870381 951682991120535813326393)
                      ·
                        rfl

theorem cell23_1853396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1853396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853396 prefixEnd_1853396 := by exact prefixLift 1853396
  have htrace : WordTrace (prefixWord ++ tailWord_1853396) baseStart_1853396 baseEnd_1853396 := by
    simpa [prefixWord, tailWord_1853396, baseEnd_1853396] using wordTrace_append hprefix tailTrace_1853396
  have hstable : (prefixWord ++ tailWord_1853396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853396).length < 2 ^ (prefixWord ++ tailWord_1853396).sum := by decide
  have hdescent : baseEnd_1853396 < baseStart_1853396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853409 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1853409 : Nat := 118140960795 + 1853409 * 2 ^ 59
def prefixEnd_1853409 : Nat := 4983230072969 + 3 ^ 40 * 1853409 * 2
def baseEnd_1853409 : Nat := 951689666369044262463833

theorem tailTrace_1853409 : CollatzResearch.WordTrace tailWord_1853409 prefixEnd_1853409 951689666369044262463833 := by
  unfold tailWord_1853409
  simp only [CollatzResearch.WordTrace]
  refine ⟨67599379742423204901507281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45066253161615469934338187 67599379742423204901507281)
  ·
    refine ⟨50699534806817403676130461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67599379742423204901507281 50699534806817403676130461)
    ·
      refine ⟨19012325552556526378548923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50699534806817403676130461 19012325552556526378548923)
      ·
        refine ⟨28518488328834789567823385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19012325552556526378548923 28518488328834789567823385)
        ·
          refine ⟨21388866246626092175867539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28518488328834789567823385 21388866246626092175867539)
          ·
            refine ⟨32083299369939138263801309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21388866246626092175867539 32083299369939138263801309)
            ·
              refine ⟨12031237263727176848925491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32083299369939138263801309 12031237263727176848925491)
              ·
                refine ⟨18046855895590765273388237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12031237263727176848925491 18046855895590765273388237)
                ·
                  refine ⟨6767570960846536977520589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18046855895590765273388237 6767570960846536977520589)
                  ·
                    refine ⟨2537839110317451366570221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6767570960846536977520589 2537839110317451366570221)
                    ·
                      refine ⟨951689666369044262463833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537839110317451366570221 951689666369044262463833)
                      ·
                        rfl

theorem cell23_1853409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1853409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853409 prefixEnd_1853409 := by exact prefixLift 1853409
  have htrace : WordTrace (prefixWord ++ tailWord_1853409) baseStart_1853409 baseEnd_1853409 := by
    simpa [prefixWord, tailWord_1853409, baseEnd_1853409] using wordTrace_append hprefix tailTrace_1853409
  have hstable : (prefixWord ++ tailWord_1853409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853409).length < 2 ^ (prefixWord ++ tailWord_1853409).sum := by decide
  have hdescent : baseEnd_1853409 < baseStart_1853409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853421 : List Nat := [1, 5, 1, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1853421 : Nat := 118140960795 + 1853421 * 2 ^ 59
def prefixEnd_1853421 : Nat := 4983230072969 + 3 ^ 40 * 1853421 * 2
def baseEnd_1853421 : Nat := 951695828136898215513779

theorem tailTrace_1853421 : CollatzResearch.WordTrace tailWord_1853421 prefixEnd_1853421 951695828136898215513779 := by
  unfold tailWord_1853421
  simp only [CollatzResearch.WordTrace]
  refine ⟨67599817418379730950944117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45066544945586487300629411 67599817418379730950944117)
  ·
    refine ⟨6337482882973099776651011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67599817418379730950944117 6337482882973099776651011)
    ·
      refine ⟨9506224324459649664976517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337482882973099776651011 9506224324459649664976517)
      ·
        refine ⟨1782417060836184312183097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9506224324459649664976517 1782417060836184312183097)
        ·
          refine ⟨1336812795627138234137323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782417060836184312183097 1336812795627138234137323)
          ·
            refine ⟨2005219193440707351205985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336812795627138234137323 2005219193440707351205985)
            ·
              refine ⟨1503914395080530513404489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005219193440707351205985 1503914395080530513404489)
              ·
                refine ⟨1127935796310397885053367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1503914395080530513404489 1127935796310397885053367)
                ·
                  refine ⟨1691903694465596827580051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127935796310397885053367 1691903694465596827580051)
                  ·
                    refine ⟨2537855541698395241370077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1691903694465596827580051 2537855541698395241370077)
                    ·
                      refine ⟨951695828136898215513779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2537855541698395241370077 951695828136898215513779)
                      ·
                        rfl

theorem cell23_1853421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1853421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853421 prefixEnd_1853421 := by exact prefixLift 1853421
  have htrace : WordTrace (prefixWord ++ tailWord_1853421) baseStart_1853421 baseEnd_1853421 := by
    simpa [prefixWord, tailWord_1853421, baseEnd_1853421] using wordTrace_append hprefix tailTrace_1853421
  have hstable : (prefixWord ++ tailWord_1853421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853421).length < 2 ^ (prefixWord ++ tailWord_1853421).sum := by decide
  have hdescent : baseEnd_1853421 < baseStart_1853421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853436 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_1853436 : Nat := 118140960795 + 1853436 * 2 ^ 59
def prefixEnd_1853436 : Nat := 4983230072969 + 3 ^ 40 * 1853436 * 2
def baseEnd_1853436 : Nat := 951703530346715656826209

theorem tailTrace_1853436 : CollatzResearch.WordTrace tailWord_1853436 prefixEnd_1853436 951703530346715656826209 := by
  unfold tailWord_1853436
  simp only [CollatzResearch.WordTrace]
  refine ⟨33800182256662694256370081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45066909675550259008493441 33800182256662694256370081)
  ·
    refine ⟨25350136692497020692277561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33800182256662694256370081 25350136692497020692277561)
    ·
      refine ⟨19012602519372765519208171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25350136692497020692277561 19012602519372765519208171)
      ·
        refine ⟨28518903779059148278812257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19012602519372765519208171 28518903779059148278812257)
        ·
          refine ⟨21389177834294361209109193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28518903779059148278812257 21389177834294361209109193)
          ·
            refine ⟨16041883375720770906831895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21389177834294361209109193 16041883375720770906831895)
            ·
              refine ⟨24062825063581156360247843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16041883375720770906831895 24062825063581156360247843)
              ·
                refine ⟨36094237595371734540371765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24062825063581156360247843 36094237595371734540371765)
                ·
                  refine ⟨3383834774566100113159853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36094237595371734540371765 3383834774566100113159853)
                  ·
                    refine ⟨1268938040462287542434945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383834774566100113159853 1268938040462287542434945)
                    ·
                      refine ⟨951703530346715656826209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268938040462287542434945 951703530346715656826209)
                      ·
                        rfl

theorem cell23_1853436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_1853436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853436 prefixEnd_1853436 := by exact prefixLift 1853436
  have htrace : WordTrace (prefixWord ++ tailWord_1853436) baseStart_1853436 baseEnd_1853436 := by
    simpa [prefixWord, tailWord_1853436, baseEnd_1853436] using wordTrace_append hprefix tailTrace_1853436
  have hstable : (prefixWord ++ tailWord_1853436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853436).length < 2 ^ (prefixWord ++ tailWord_1853436).sum := by decide
  have hdescent : baseEnd_1853436 < baseStart_1853436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853483 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 2, 2, 2]
def baseStart_1853483 : Nat := 118140960795 + 1853483 * 2 ^ 59
def prefixEnd_1853483 : Nat := 4983230072969 + 3 ^ 40 * 1853483 * 2
def baseEnd_1853483 : Nat := 951727663937476972938493

theorem tailTrace_1853483 : CollatzResearch.WordTrace tailWord_1853483 prefixEnd_1853483 951727663937476972938493 := by
  unfold tailWord_1853483
  simp only [CollatzResearch.WordTrace]
  refine ⟨67602078744155115539701103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45068052496103410359800735 67602078744155115539701103)
  ·
    refine ⟨101403118116232673309551655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67602078744155115539701103 101403118116232673309551655)
    ·
      refine ⟨152104677174349009964327483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101403118116232673309551655 152104677174349009964327483)
      ·
        refine ⟨228157015761523514946491225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152104677174349009964327483 228157015761523514946491225)
        ·
          refine ⟨171117761821142636209868419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228157015761523514946491225 171117761821142636209868419)
          ·
            refine ⟨256676642731713954314802629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171117761821142636209868419 256676642731713954314802629)
            ·
              refine ⟨48126870512196366434025493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256676642731713954314802629 48126870512196366434025493)
              ·
                refine ⟨2255947055259204676594945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48126870512196366434025493 2255947055259204676594945)
                ·
                  refine ⟨1691960291444403507446209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2255947055259204676594945 1691960291444403507446209)
                  ·
                    refine ⟨1268970218583302630584657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1691960291444403507446209 1268970218583302630584657)
                    ·
                      refine ⟨951727663937476972938493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1268970218583302630584657 951727663937476972938493)
                      ·
                        rfl

theorem cell23_1853483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 2, 2].length) (baseStart_1853483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853483 prefixEnd_1853483 := by exact prefixLift 1853483
  have htrace : WordTrace (prefixWord ++ tailWord_1853483) baseStart_1853483 baseEnd_1853483 := by
    simpa [prefixWord, tailWord_1853483, baseEnd_1853483] using wordTrace_append hprefix tailTrace_1853483
  have hstable : (prefixWord ++ tailWord_1853483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853483).length < 2 ^ (prefixWord ++ tailWord_1853483).sum := by decide
  have hdescent : baseEnd_1853483 < baseStart_1853483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853489 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 7]
def baseStart_1853489 : Nat := 118140960795 + 1853489 * 2 ^ 59
def prefixEnd_1853489 : Nat := 4983230072969 + 3 ^ 40 * 1853489 * 2
def baseEnd_1853489 : Nat := 105747860535711549940385

theorem tailTrace_1853489 : CollatzResearch.WordTrace tailWord_1853489 prefixEnd_1853489 105747860535711549940385 := by
  unfold tailWord_1853489
  simp only [CollatzResearch.WordTrace]
  refine ⟨67602297582133378564419521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45068198388088919042946347 67602297582133378564419521)
  ·
    refine ⟨50701723186600033923314641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67602297582133378564419521 50701723186600033923314641)
    ·
      refine ⟨38026292389950025442485981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50701723186600033923314641 38026292389950025442485981)
      ·
        refine ⟨14259859646231259540932243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38026292389950025442485981 14259859646231259540932243)
        ·
          refine ⟨21389789469346889311398365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14259859646231259540932243 21389789469346889311398365)
          ·
            refine ⟨8021171051005083491774387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21389789469346889311398365 8021171051005083491774387)
            ·
              refine ⟨12031756576507625237661581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021171051005083491774387 12031756576507625237661581)
              ·
                refine ⟨4511908716190359464123093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12031756576507625237661581 4511908716190359464123093)
                ·
                  refine ⟨105747860535711549940385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4511908716190359464123093 105747860535711549940385)
                  ·
                    rfl

theorem cell23_1853489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 7].length) (baseStart_1853489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853489 prefixEnd_1853489 := by exact prefixLift 1853489
  have htrace : WordTrace (prefixWord ++ tailWord_1853489) baseStart_1853489 baseEnd_1853489 := by
    simpa [prefixWord, tailWord_1853489, baseEnd_1853489] using wordTrace_append hprefix tailTrace_1853489
  have hstable : (prefixWord ++ tailWord_1853489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853489).length < 2 ^ (prefixWord ++ tailWord_1853489).sum := by decide
  have hdescent : baseEnd_1853489 < baseStart_1853489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853529 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1853529 : Nat := 118140960795 + 1853529 * 2 ^ 59
def prefixEnd_1853529 : Nat := 4983230072969 + 3 ^ 40 * 1853529 * 2
def baseEnd_1853529 : Nat := 951751284047583792963281

theorem tailTrace_1853529 : CollatzResearch.WordTrace tailWord_1853529 prefixEnd_1853529 951751284047583792963281 := by
  unfold tailWord_1853529
  simp only [CollatzResearch.WordTrace]
  refine ⟨67603756501988465395875641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45069171001325643597250427 67603756501988465395875641)
  ·
    refine ⟨50702817376491349046906731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67603756501988465395875641 50702817376491349046906731)
    ·
      refine ⟨76054226064737023570360097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50702817376491349046906731 76054226064737023570360097)
      ·
        refine ⟨57040669548552767677770073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76054226064737023570360097 57040669548552767677770073)
        ·
          refine ⟨42780502161414575758327555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57040669548552767677770073 42780502161414575758327555)
          ·
            refine ⟨64170753242121863637491333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42780502161414575758327555 64170753242121863637491333)
            ·
              refine ⟨12032016232897849432029625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64170753242121863637491333 12032016232897849432029625)
              ·
                refine ⟨9024012174673387074022219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12032016232897849432029625 9024012174673387074022219)
                ·
                  refine ⟨13536018262010080611033329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024012174673387074022219 13536018262010080611033329)
                  ·
                    refine ⟨10152013696507560458274997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13536018262010080611033329 10152013696507560458274997)
                    ·
                      refine ⟨951751284047583792963281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10152013696507560458274997 951751284047583792963281)
                      ·
                        rfl

theorem cell23_1853529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1853529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853529 prefixEnd_1853529 := by exact prefixLift 1853529
  have htrace : WordTrace (prefixWord ++ tailWord_1853529) baseStart_1853529 baseEnd_1853529 := by
    simpa [prefixWord, tailWord_1853529, baseEnd_1853529] using wordTrace_append hprefix tailTrace_1853529
  have hstable : (prefixWord ++ tailWord_1853529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853529).length < 2 ^ (prefixWord ++ tailWord_1853529).sum := by decide
  have hdescent : baseEnd_1853529 < baseStart_1853529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853536 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 2, 5]
def baseStart_1853536 : Nat := 118140960795 + 1853536 * 2 ^ 59
def prefixEnd_1853536 : Nat := 4983230072969 + 3 ^ 40 * 1853536 * 2
def baseEnd_1853536 : Nat := 317251626137388421858583

theorem tailTrace_1853536 : CollatzResearch.WordTrace tailWord_1853536 prefixEnd_1853536 317251626137388421858583 := by
  unfold tailWord_1853536
  simp only [CollatzResearch.WordTrace]
  refine ⟨33802005906481552795690231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45069341208642070394253641 33802005906481552795690231)
  ·
    refine ⟨50703008859722329193535347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33802005906481552795690231 50703008859722329193535347)
    ·
      refine ⟨76054513289583493790303021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50703008859722329193535347 76054513289583493790303021)
      ·
        refine ⟨28520442483593810171363633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76054513289583493790303021 28520442483593810171363633)
        ·
          refine ⟨21390331862695357628522725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28520442483593810171363633 21390331862695357628522725)
          ·
            refine ⟨4010687224255379555348011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21390331862695357628522725 4010687224255379555348011)
            ·
              refine ⟨6016030836383069333022017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010687224255379555348011 6016030836383069333022017)
              ·
                refine ⟨4512023127287301999766513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016030836383069333022017 4512023127287301999766513)
                ·
                  refine ⟨3384017345465476499824885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4512023127287301999766513 3384017345465476499824885)
                  ·
                    refine ⟨317251626137388421858583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3384017345465476499824885 317251626137388421858583)
                    ·
                      rfl

theorem cell23_1853536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_1853536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853536 prefixEnd_1853536 := by exact prefixLift 1853536
  have htrace : WordTrace (prefixWord ++ tailWord_1853536) baseStart_1853536 baseEnd_1853536 := by
    simpa [prefixWord, tailWord_1853536, baseEnd_1853536] using wordTrace_append hprefix tailTrace_1853536
  have hstable : (prefixWord ++ tailWord_1853536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853536).length < 2 ^ (prefixWord ++ tailWord_1853536).sum := by decide
  have hdescent : baseEnd_1853536 < baseStart_1853536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853573 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_1853573 : Nat := 118140960795 + 1853573 * 2 ^ 59
def prefixEnd_1853573 : Nat := 4983230072969 + 3 ^ 40 * 1853573 * 2
def baseEnd_1853573 : Nat := 951773877196381620813079

theorem tailTrace_1853573 : CollatzResearch.WordTrace tailWord_1853573 prefixEnd_1853573 951773877196381620813079 := by
  unfold tailWord_1853573
  simp only [CollatzResearch.WordTrace]
  refine ⟨67605361313829060910477373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45070240875886040606984915 67605361313829060910477373)
  ·
    refine ⟨25352010492685897841429015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67605361313829060910477373 25352010492685897841429015)
    ·
      refine ⟨38028015739028846762143523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25352010492685897841429015 38028015739028846762143523)
      ·
        refine ⟨57042023608543270143215285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38028015739028846762143523 57042023608543270143215285)
        ·
          refine ⟨5347689713300931575926433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57042023608543270143215285 5347689713300931575926433)
          ·
            refine ⟨4010767284975698681944825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5347689713300931575926433 4010767284975698681944825)
            ·
              refine ⟨3008075463731774011458619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4010767284975698681944825 3008075463731774011458619)
              ·
                refine ⟨4512113195597661017187929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008075463731774011458619 4512113195597661017187929)
                ·
                  refine ⟨3384084896698245762890947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4512113195597661017187929 3384084896698245762890947)
                  ·
                    refine ⟨5076127345047368644336421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3384084896698245762890947 5076127345047368644336421)
                    ·
                      refine ⟨951773877196381620813079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5076127345047368644336421 951773877196381620813079)
                      ·
                        rfl

theorem cell23_1853573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_1853573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853573 prefixEnd_1853573 := by exact prefixLift 1853573
  have htrace : WordTrace (prefixWord ++ tailWord_1853573) baseStart_1853573 baseEnd_1853573 := by
    simpa [prefixWord, tailWord_1853573, baseEnd_1853573] using wordTrace_append hprefix tailTrace_1853573
  have hstable : (prefixWord ++ tailWord_1853573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853573).length < 2 ^ (prefixWord ++ tailWord_1853573).sum := by decide
  have hdescent : baseEnd_1853573 < baseStart_1853573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853586 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1853586 : Nat := 118140960795 + 1853586 * 2 ^ 59
def prefixEnd_1853586 : Nat := 4983230072969 + 3 ^ 40 * 1853586 * 2
def baseEnd_1853586 : Nat := 951780552444890069950519

theorem tailTrace_1853586 : CollatzResearch.WordTrace tailWord_1853586 prefixEnd_1853586 951780552444890069950519 := by
  unfold tailWord_1853586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901458865695491032675153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45070556975187976087133741 16901458865695491032675153)
  ·
    refine ⟨12676094149271618274506365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16901458865695491032675153 12676094149271618274506365)
    ·
      refine ⟨4753535305976856852939887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12676094149271618274506365 4753535305976856852939887)
      ·
        refine ⟨7130302958965285279409831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753535305976856852939887 7130302958965285279409831)
        ·
          refine ⟨10695454438447927919114747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7130302958965285279409831 10695454438447927919114747)
          ·
            refine ⟨16043181657671891878672121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10695454438447927919114747 16043181657671891878672121)
            ·
              refine ⟨12032386243253918909004091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16043181657671891878672121 12032386243253918909004091)
              ·
                refine ⟨18048579364880878363506137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12032386243253918909004091 18048579364880878363506137)
                ·
                  refine ⟨13536434523660658772629603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18048579364880878363506137 13536434523660658772629603)
                  ·
                    refine ⟨20304651785490988158944405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13536434523660658772629603 20304651785490988158944405)
                    ·
                      refine ⟨951780552444890069950519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20304651785490988158944405 951780552444890069950519)
                      ·
                        rfl

theorem cell23_1853586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1853586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853586 prefixEnd_1853586 := by exact prefixLift 1853586
  have htrace : WordTrace (prefixWord ++ tailWord_1853586) baseStart_1853586 baseEnd_1853586 := by
    simpa [prefixWord, tailWord_1853586, baseEnd_1853586] using wordTrace_append hprefix tailTrace_1853586
  have hstable : (prefixWord ++ tailWord_1853586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853586).length < 2 ^ (prefixWord ++ tailWord_1853586).sum := by decide
  have hdescent : baseEnd_1853586 < baseStart_1853586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853600 : List Nat := [2, 1, 1, 4, 2, 3, 1, 4, 1, 4]
def baseStart_1853600 : Nat := 118140960795 + 1853600 * 2 ^ 59
def prefixEnd_1853600 : Nat := 4983230072969 + 3 ^ 40 * 1853600 * 2
def baseEnd_1853600 : Nat := 317262580391351005058485

theorem tailTrace_1853600 : CollatzResearch.WordTrace tailWord_1853600 prefixEnd_1853600 317262580391351005058485 := by
  unfold tailWord_1853600
  simp only [CollatzResearch.WordTrace]
  refine ⟨33803173042365622260855127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45070897389820829681140169 33803173042365622260855127)
  ·
    refine ⟨50704759563548433391282691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33803173042365622260855127 50704759563548433391282691)
    ·
      refine ⟨76057139345322650086924037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50704759563548433391282691 76057139345322650086924037)
      ·
        refine ⟨14260713627247996891298257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76057139345322650086924037 14260713627247996891298257)
        ·
          refine ⟨10695535220435997668473693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14260713627247996891298257 10695535220435997668473693)
          ·
            refine ⟨4010825707663499125677635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10695535220435997668473693 4010825707663499125677635)
            ·
              refine ⟨6016238561495248688516453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010825707663499125677635 6016238561495248688516453)
              ·
                refine ⟨1128044730280359129096835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6016238561495248688516453 1128044730280359129096835)
                ·
                  refine ⟨1692067095420538693645253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128044730280359129096835 1692067095420538693645253)
                  ·
                    refine ⟨317262580391351005058485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692067095420538693645253 317262580391351005058485)
                    ·
                      rfl

theorem cell23_1853600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 4].length) (baseStart_1853600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853600 prefixEnd_1853600 := by exact prefixLift 1853600
  have htrace : WordTrace (prefixWord ++ tailWord_1853600) baseStart_1853600 baseEnd_1853600 := by
    simpa [prefixWord, tailWord_1853600, baseEnd_1853600] using wordTrace_append hprefix tailTrace_1853600
  have hstable : (prefixWord ++ tailWord_1853600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853600).length < 2 ^ (prefixWord ++ tailWord_1853600).sum := by decide
  have hdescent : baseEnd_1853600 < baseStart_1853600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853613 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1853613 : Nat := 118140960795 + 1853613 * 2 ^ 59
def prefixEnd_1853613 : Nat := 4983230072969 + 3 ^ 40 * 1853613 * 2
def baseEnd_1853613 : Nat := 105754935158062384923655

theorem tailTrace_1853613 : CollatzResearch.WordTrace tailWord_1853613 prefixEnd_1853613 105754935158062384923655 := by
  unfold tailWord_1853613
  simp only [CollatzResearch.WordTrace]
  refine ⟨67606820233684147741933493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45071213489122765161288995 67606820233684147741933493)
  ·
    refine ⟨6338139396907888850806265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67606820233684147741933493 6338139396907888850806265)
    ·
      refine ⟨4753604547680916638104699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6338139396907888850806265 4753604547680916638104699)
      ·
        refine ⟨7130406821521374957157049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753604547680916638104699 7130406821521374957157049)
        ·
          refine ⟨5347805116141031217867787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7130406821521374957157049 5347805116141031217867787)
          ·
            refine ⟨8021707674211546826801681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347805116141031217867787 8021707674211546826801681)
            ·
              refine ⟨6016280755658660120101261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8021707674211546826801681 6016280755658660120101261)
              ·
                refine ⟨2256105283371997545037973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6016280755658660120101261 2256105283371997545037973)
                ·
                  refine ⟨105754935158062384923655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2256105283371997545037973 105754935158062384923655)
                  ·
                    rfl

theorem cell23_1853613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1853613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853613 prefixEnd_1853613 := by exact prefixLift 1853613
  have htrace : WordTrace (prefixWord ++ tailWord_1853613) baseStart_1853613 baseEnd_1853613 := by
    simpa [prefixWord, tailWord_1853613, baseEnd_1853613] using wordTrace_append hprefix tailTrace_1853613
  have hstable : (prefixWord ++ tailWord_1853613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853613).length < 2 ^ (prefixWord ++ tailWord_1853613).sum := by decide
  have hdescent : baseEnd_1853613 < baseStart_1853613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853619 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7]
def baseStart_1853619 : Nat := 118140960795 + 1853619 * 2 ^ 59
def prefixEnd_1853619 : Nat := 4983230072969 + 3 ^ 40 * 1853619 * 2
def baseEnd_1853619 : Nat := 951797497306488440837867

theorem tailTrace_1853619 : CollatzResearch.WordTrace tailWord_1853619 prefixEnd_1853619 951797497306488440837867 := by
  unfold tailWord_1853619
  simp only [CollatzResearch.WordTrace]
  refine ⟨67607039071662410766651911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45071359381108273844434607 67607039071662410766651911)
  ·
    refine ⟨101410558607493616149977867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67607039071662410766651911 101410558607493616149977867)
    ·
      refine ⟨152115837911240424224966801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101410558607493616149977867 152115837911240424224966801)
      ·
        refine ⟨114086878433430318168725101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152115837911240424224966801 114086878433430318168725101)
        ·
          refine ⟨42782579412536369313271913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114086878433430318168725101 42782579412536369313271913)
          ·
            refine ⟨32086934559402276984953935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42782579412536369313271913 32086934559402276984953935)
            ·
              refine ⟨48130401839103415477430903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32086934559402276984953935 48130401839103415477430903)
              ·
                refine ⟨72195602758655123216146355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48130401839103415477430903 72195602758655123216146355)
                ·
                  refine ⟨108293404137982684824219533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72195602758655123216146355 108293404137982684824219533)
                  ·
                    refine ⟨40610026551743506809082325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108293404137982684824219533 40610026551743506809082325)
                    ·
                      refine ⟨951797497306488440837867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40610026551743506809082325 951797497306488440837867)
                      ·
                        rfl

theorem cell23_1853619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_1853619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853619 prefixEnd_1853619 := by exact prefixLift 1853619
  have htrace : WordTrace (prefixWord ++ tailWord_1853619) baseStart_1853619 baseEnd_1853619 := by
    simpa [prefixWord, tailWord_1853619, baseEnd_1853619] using wordTrace_append hprefix tailTrace_1853619
  have hstable : (prefixWord ++ tailWord_1853619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853619).length < 2 ^ (prefixWord ++ tailWord_1853619).sum := by decide
  have hdescent : baseEnd_1853619 < baseStart_1853619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853623 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 3]
def baseStart_1853623 : Nat := 118140960795 + 1853623 * 2 ^ 59
def prefixEnd_1853623 : Nat := 4983230072969 + 3 ^ 40 * 1853623 * 2
def baseEnd_1853623 : Nat := 951799551229106425187849

theorem tailTrace_1853623 : CollatzResearch.WordTrace tailWord_1853623 prefixEnd_1853623 951799551229106425187849 := by
  unfold tailWord_1853623
  simp only [CollatzResearch.WordTrace]
  refine ⟨67607184963647919449797523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45071456642431946299865015 67607184963647919449797523)
  ·
    refine ⟨101410777445471879174696285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67607184963647919449797523 101410777445471879174696285)
    ·
      refine ⟨38029041542051954690511107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101410777445471879174696285 38029041542051954690511107)
      ·
        refine ⟨57043562313077932035766661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38029041542051954690511107 57043562313077932035766661)
        ·
          refine ⟨10695667933702112256706249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57043562313077932035766661 10695667933702112256706249)
          ·
            refine ⟨8021750950276584192529687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10695667933702112256706249 8021750950276584192529687)
            ·
              refine ⟨12032626425414876288794531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021750950276584192529687 12032626425414876288794531)
              ·
                refine ⟨18048939638122314433191797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12032626425414876288794531 18048939638122314433191797)
                ·
                  refine ⟨1692088091073966978111731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18048939638122314433191797 1692088091073966978111731)
                  ·
                    refine ⟨2538132136610950467167597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1692088091073966978111731 2538132136610950467167597)
                    ·
                      refine ⟨951799551229106425187849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2538132136610950467167597 951799551229106425187849)
                      ·
                        rfl

theorem cell23_1853623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_1853623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853623 prefixEnd_1853623 := by exact prefixLift 1853623
  have htrace : WordTrace (prefixWord ++ tailWord_1853623) baseStart_1853623 baseEnd_1853623 := by
    simpa [prefixWord, tailWord_1853623, baseEnd_1853623] using wordTrace_append hprefix tailTrace_1853623
  have hstable : (prefixWord ++ tailWord_1853623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853623).length < 2 ^ (prefixWord ++ tailWord_1853623).sum := by decide
  have hdescent : baseEnd_1853623 < baseStart_1853623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853626 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_1853626 : Nat := 118140960795 + 1853626 * 2 ^ 59
def prefixEnd_1853626 : Nat := 4983230072969 + 3 ^ 40 * 1853626 * 2
def baseEnd_1853626 : Nat := 317267030557023304483445

theorem tailTrace_1853626 : CollatzResearch.WordTrace tailWord_1853626 prefixEnd_1853626 317267030557023304483445 := by
  unfold tailWord_1853626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901823595659262740539183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45071529588424700641437821 16901823595659262740539183)
  ·
    refine ⟨25352735393488894110808775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16901823595659262740539183 25352735393488894110808775)
    ·
      refine ⟨38029103090233341166213163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25352735393488894110808775 38029103090233341166213163)
      ·
        refine ⟨57043654635350011749319745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38029103090233341166213163 57043654635350011749319745)
        ·
          refine ⟨42782740976512508811989809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57043654635350011749319745 42782740976512508811989809)
          ·
            refine ⟨32087055732384381608992357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42782740976512508811989809 32087055732384381608992357)
            ·
              refine ⟨6016322949822071551686067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32087055732384381608992357 6016322949822071551686067)
              ·
                refine ⟨9024484424733107327529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016322949822071551686067 9024484424733107327529101)
                ·
                  refine ⟨3384181659274915247823413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9024484424733107327529101 3384181659274915247823413)
                  ·
                    refine ⟨317267030557023304483445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3384181659274915247823413 317267030557023304483445)
                    ·
                      rfl

theorem cell23_1853626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_1853626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853626 prefixEnd_1853626 := by exact prefixLift 1853626
  have htrace : WordTrace (prefixWord ++ tailWord_1853626) baseStart_1853626 baseEnd_1853626 := by
    simpa [prefixWord, tailWord_1853626, baseEnd_1853626] using wordTrace_append hprefix tailTrace_1853626
  have hstable : (prefixWord ++ tailWord_1853626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853626).length < 2 ^ (prefixWord ++ tailWord_1853626).sum := by decide
  have hdescent : baseEnd_1853626 < baseStart_1853626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853634 : List Nat := [3, 5, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1853634 : Nat := 118140960795 + 1853634 * 2 ^ 59
def prefixEnd_1853634 : Nat := 4983230072969 + 3 ^ 40 * 1853634 * 2
def baseEnd_1853634 : Nat := 317268399838768627383433

theorem tailTrace_1853634 : CollatzResearch.WordTrace tailWord_1853634 prefixEnd_1853634 317268399838768627383433 := by
  unfold tailWord_1853634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901896541652017082111989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45071724111072045552298637 16901896541652017082111989)
  ·
    refine ⟨1584552800779876601447999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16901896541652017082111989 1584552800779876601447999)
    ·
      refine ⟨2376829201169814902171999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584552800779876601447999 2376829201169814902171999)
      ·
        refine ⟨3565243801754722353257999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376829201169814902171999 3565243801754722353257999)
        ·
          refine ⟨5347865702632083529886999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565243801754722353257999 5347865702632083529886999)
          ·
            refine ⟨8021798553948125294830499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347865702632083529886999 8021798553948125294830499)
            ·
              refine ⟨12032697830922187942245749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021798553948125294830499 12032697830922187942245749)
              ·
                refine ⟨1128065421648955119585539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12032697830922187942245749 1128065421648955119585539)
                ·
                  refine ⟨1692098132473432679378309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128065421648955119585539 1692098132473432679378309)
                  ·
                    refine ⟨317268399838768627383433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692098132473432679378309 317268399838768627383433)
                    ·
                      rfl

theorem cell23_1853634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1853634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853634 prefixEnd_1853634 := by exact prefixLift 1853634
  have htrace : WordTrace (prefixWord ++ tailWord_1853634) baseStart_1853634 baseEnd_1853634 := by
    simpa [prefixWord, tailWord_1853634, baseEnd_1853634] using wordTrace_append hprefix tailTrace_1853634
  have hstable : (prefixWord ++ tailWord_1853634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853634).length < 2 ^ (prefixWord ++ tailWord_1853634).sum := by decide
  have hdescent : baseEnd_1853634 < baseStart_1853634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853676 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_1853676 : Nat := 118140960795 + 1853676 * 2 ^ 59
def prefixEnd_1853676 : Nat := 4983230072969 + 3 ^ 40 * 1853676 * 2
def baseEnd_1853676 : Nat := 951826765703794717825105

theorem tailTrace_1853676 : CollatzResearch.WordTrace tailWord_1853676 prefixEnd_1853676 951826765703794717825105 := by
  unfold tailWord_1853676
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804559016227954750738441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45072745354970606334317921 33804559016227954750738441)
  ·
    refine ⟨25353419262170966063053831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33804559016227954750738441 25353419262170966063053831)
    ·
      refine ⟨38030128893256449094580747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25353419262170966063053831 38030128893256449094580747)
      ·
        refine ⟨57045193339884673641871121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38030128893256449094580747 57045193339884673641871121)
        ·
          refine ⟨42783895004913505231403341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57045193339884673641871121 42783895004913505231403341)
          ·
            refine ⟨16043960626842564461776253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42783895004913505231403341 16043960626842564461776253)
            ·
              refine ⟨6016485235065961673166095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16043960626842564461776253 6016485235065961673166095)
              ·
                refine ⟨9024727852598942509749143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016485235065961673166095 9024727852598942509749143)
                ·
                  refine ⟨13537091778898413764623715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9024727852598942509749143 13537091778898413764623715)
                  ·
                    refine ⟨20305637668347620646935573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13537091778898413764623715 20305637668347620646935573)
                    ·
                      refine ⟨951826765703794717825105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20305637668347620646935573 951826765703794717825105)
                      ·
                        rfl

theorem cell23_1853676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_1853676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853676 prefixEnd_1853676 := by exact prefixLift 1853676
  have htrace : WordTrace (prefixWord ++ tailWord_1853676) baseStart_1853676 baseEnd_1853676 := by
    simpa [prefixWord, tailWord_1853676, baseEnd_1853676] using wordTrace_append hprefix tailTrace_1853676
  have hstable : (prefixWord ++ tailWord_1853676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853676).length < 2 ^ (prefixWord ++ tailWord_1853676).sum := by decide
  have hdescent : baseEnd_1853676 < baseStart_1853676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853700 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1853700 : Nat := 118140960795 + 1853700 * 2 ^ 59
def prefixEnd_1853700 : Nat := 4983230072969 + 3 ^ 40 * 1853700 * 2
def baseEnd_1853700 : Nat := 951839089239502623924995

theorem tailTrace_1853700 : CollatzResearch.WordTrace tailWord_1853700 prefixEnd_1853700 951839089239502623924995 := by
  unfold tailWord_1853700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804996692184480800175277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45073328922912641066900369 33804996692184480800175277)
  ·
    refine ⟨12676873759569180300065729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33804996692184480800175277 12676873759569180300065729)
    ·
      refine ⟨9507655319676885225049297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12676873759569180300065729 9507655319676885225049297)
      ·
        refine ⟨7130741489757663918786973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9507655319676885225049297 7130741489757663918786973)
        ·
          refine ⟨2674028058659123969545115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7130741489757663918786973 2674028058659123969545115)
          ·
            refine ⟨4011042087988685954317673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674028058659123969545115 4011042087988685954317673)
            ·
              refine ⟨3008281565991514465738255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011042087988685954317673 3008281565991514465738255)
              ·
                refine ⟨4512422348987271698607383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008281565991514465738255 4512422348987271698607383)
                ·
                  refine ⟨6768633523480907547911075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512422348987271698607383 6768633523480907547911075)
                  ·
                    refine ⟨10152950285221361321866613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6768633523480907547911075 10152950285221361321866613)
                    ·
                      refine ⟨951839089239502623924995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10152950285221361321866613 951839089239502623924995)
                      ·
                        rfl

theorem cell23_1853700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1853700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853700 prefixEnd_1853700 := by exact prefixLift 1853700
  have htrace : WordTrace (prefixWord ++ tailWord_1853700) baseStart_1853700 baseEnd_1853700 := by
    simpa [prefixWord, tailWord_1853700, baseEnd_1853700] using wordTrace_append hprefix tailTrace_1853700
  have hstable : (prefixWord ++ tailWord_1853700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853700).length < 2 ^ (prefixWord ++ tailWord_1853700).sum := by decide
  have hdescent : baseEnd_1853700 < baseStart_1853700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853783 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1853783 : Nat := 118140960795 + 1853783 * 2 ^ 59
def prefixEnd_1853783 : Nat := 4983230072969 + 3 ^ 40 * 1853783 * 2
def baseEnd_1853783 : Nat := 951881708133825799187113

theorem tailTrace_1853783 : CollatzResearch.WordTrace tailWord_1853783 prefixEnd_1853783 951881708133825799187113 := by
  unfold tailWord_1853783
  simp only [CollatzResearch.WordTrace]
  refine ⟨67613020643068266775622003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45075347095378844517081335 67613020643068266775622003)
  ·
    refine ⟨101419530964602400163433005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67613020643068266775622003 101419530964602400163433005)
    ·
      refine ⟨38032324111725900061287377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101419530964602400163433005 38032324111725900061287377)
      ·
        refine ⟨28524243083794425045965533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38032324111725900061287377 28524243083794425045965533)
        ·
          refine ⟨10696591156422909392237075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28524243083794425045965533 10696591156422909392237075)
          ·
            refine ⟨16044886734634364088355613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696591156422909392237075 16044886734634364088355613)
            ·
              refine ⟨6016832525487886533133355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16044886734634364088355613 6016832525487886533133355)
              ·
                refine ⟨9025248788231829799700033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016832525487886533133355 9025248788231829799700033)
                ·
                  refine ⟨6768936591173872349775025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9025248788231829799700033 6768936591173872349775025)
                  ·
                    refine ⟨5076702443380404262331269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6768936591173872349775025 5076702443380404262331269)
                    ·
                      refine ⟨951881708133825799187113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5076702443380404262331269 951881708133825799187113)
                      ·
                        rfl

theorem cell23_1853783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1853783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853783 prefixEnd_1853783 := by exact prefixLift 1853783
  have htrace : WordTrace (prefixWord ++ tailWord_1853783) baseStart_1853783 baseEnd_1853783 := by
    simpa [prefixWord, tailWord_1853783, baseEnd_1853783] using wordTrace_append hprefix tailTrace_1853783
  have hstable : (prefixWord ++ tailWord_1853783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853783).length < 2 ^ (prefixWord ++ tailWord_1853783).sum := by decide
  have hdescent : baseEnd_1853783 < baseStart_1853783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853810 : List Nat := [3, 2, 1, 2, 1, 3, 1, 5, 5]
def baseStart_1853810 : Nat := 118140960795 + 1853810 * 2 ^ 59
def prefixEnd_1853810 : Nat := 4983230072969 + 3 ^ 40 * 1853810 * 2
def baseEnd_1853810 : Nat := 105766174679055243727721

theorem tailTrace_1853810 : CollatzResearch.WordTrace tailWord_1853810 prefixEnd_1853810 105766174679055243727721 := by
  unfold tailWord_1853810
  simp only [CollatzResearch.WordTrace]
  refine ⟨16903501353492612596713721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45076003609313633591236589 16903501353492612596713721)
  ·
    refine ⟨12677626015119459447535291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16903501353492612596713721 12677626015119459447535291)
    ·
      refine ⟨19016439022679189171302937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12677626015119459447535291 19016439022679189171302937)
      ·
        refine ⟨14262329267009391878477203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19016439022679189171302937 14262329267009391878477203)
        ·
          refine ⟨21393493900514087817715805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14262329267009391878477203 21393493900514087817715805)
          ·
            refine ⟨8022560212692782931643427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21393493900514087817715805 8022560212692782931643427)
            ·
              refine ⟨12033840319039174397465141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8022560212692782931643427 12033840319039174397465141)
              ·
                refine ⟨1128172529909922599762357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12033840319039174397465141 1128172529909922599762357)
                ·
                  refine ⟨105766174679055243727721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1128172529909922599762357 105766174679055243727721)
                  ·
                    rfl

theorem cell23_1853810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_1853810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853810 prefixEnd_1853810 := by exact prefixLift 1853810
  have htrace : WordTrace (prefixWord ++ tailWord_1853810) baseStart_1853810 baseEnd_1853810 := by
    simpa [prefixWord, tailWord_1853810, baseEnd_1853810] using wordTrace_append hprefix tailTrace_1853810
  have hstable : (prefixWord ++ tailWord_1853810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853810).length < 2 ^ (prefixWord ++ tailWord_1853810).sum := by decide
  have hdescent : baseEnd_1853810 < baseStart_1853810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853860 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_1853860 : Nat := 118140960795 + 1853860 * 2 ^ 59
def prefixEnd_1853860 : Nat := 4983230072969 + 3 ^ 40 * 1853860 * 2
def baseEnd_1853860 : Nat := 951921246144221997924259

theorem tailTrace_1853860 : CollatzResearch.WordTrace tailWord_1853860 prefixEnd_1853860 951921246144221997924259 := by
  unfold tailWord_1853860
  simp only [CollatzResearch.WordTrace]
  refine ⟨33807914531894654463087517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45077219375859539284116689 33807914531894654463087517)
  ·
    refine ⟨12677967949460495423657819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33807914531894654463087517 12677967949460495423657819)
    ·
      refine ⟨19016951924190743135486729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12677967949460495423657819 19016951924190743135486729)
      ·
        refine ⟨14262713943143057351615047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19016951924190743135486729 14262713943143057351615047)
        ·
          refine ⟨21394070914714586027422571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14262713943143057351615047 21394070914714586027422571)
          ·
            refine ⟨32091106372071879041133857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21394070914714586027422571 32091106372071879041133857)
            ·
              refine ⟨24068329779053909280850393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32091106372071879041133857 24068329779053909280850393)
              ·
                refine ⟨18051247334290431960637795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24068329779053909280850393 18051247334290431960637795)
                ·
                  refine ⟨27076871001435647940956693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18051247334290431960637795 27076871001435647940956693)
                  ·
                    refine ⟨1269228328192295997232345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27076871001435647940956693 1269228328192295997232345)
                    ·
                      refine ⟨951921246144221997924259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269228328192295997232345 951921246144221997924259)
                      ·
                        rfl

theorem cell23_1853860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_1853860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853860 prefixEnd_1853860 := by exact prefixLift 1853860
  have htrace : WordTrace (prefixWord ++ tailWord_1853860) baseStart_1853860 baseEnd_1853860 := by
    simpa [prefixWord, tailWord_1853860, baseEnd_1853860] using wordTrace_append hprefix tailTrace_1853860
  have hstable : (prefixWord ++ tailWord_1853860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853860).length < 2 ^ (prefixWord ++ tailWord_1853860).sum := by decide
  have hdescent : baseEnd_1853860 < baseStart_1853860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853877 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1853877 : Nat := 118140960795 + 1853877 * 2 ^ 59
def prefixEnd_1853877 : Nat := 4983230072969 + 3 ^ 40 * 1853877 * 2
def baseEnd_1853877 : Nat := 951929975315348431411681

theorem tailTrace_1853877 : CollatzResearch.WordTrace tailWord_1853877 prefixEnd_1853877 951929975315348431411681 := by
  unfold tailWord_1853877
  simp only [CollatzResearch.WordTrace]
  refine ⟨67616449104727720829543885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45077632736485147219695923 67616449104727720829543885)
  ·
    refine ⟨25356168414272895311078957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67616449104727720829543885 25356168414272895311078957)
    ·
      refine ⟨9508563155352335741654609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25356168414272895311078957 9508563155352335741654609)
      ·
        refine ⟨7131422366514251806240957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9508563155352335741654609 7131422366514251806240957)
        ·
          refine ⟨2674283387442844427340359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7131422366514251806240957 2674283387442844427340359)
          ·
            refine ⟨4011425081164266641010539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674283387442844427340359 4011425081164266641010539)
            ·
              refine ⟨6017137621746399961515809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011425081164266641010539 6017137621746399961515809)
              ·
                refine ⟨4512853216309799971136857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6017137621746399961515809 4512853216309799971136857)
                ·
                  refine ⟨3384639912232349978352643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4512853216309799971136857 3384639912232349978352643)
                  ·
                    refine ⟨5076959868348524967528965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3384639912232349978352643 5076959868348524967528965)
                    ·
                      refine ⟨951929975315348431411681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5076959868348524967528965 951929975315348431411681)
                      ·
                        rfl

theorem cell23_1853877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1853877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853877 prefixEnd_1853877 := by exact prefixLift 1853877
  have htrace : WordTrace (prefixWord ++ tailWord_1853877) baseStart_1853877 baseEnd_1853877 := by
    simpa [prefixWord, tailWord_1853877, baseEnd_1853877] using wordTrace_append hprefix tailTrace_1853877
  have hstable : (prefixWord ++ tailWord_1853877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853877).length < 2 ^ (prefixWord ++ tailWord_1853877).sum := by decide
  have hdescent : baseEnd_1853877 < baseStart_1853877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853937 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 2, 3, 2]
def baseStart_1853937 : Nat := 118140960795 + 1853937 * 2 ^ 59
def prefixEnd_1853937 : Nat := 4983230072969 + 3 ^ 40 * 1853937 * 2
def baseEnd_1853937 : Nat := 951960784154618196661405

theorem tailTrace_1853937 : CollatzResearch.WordTrace tailWord_1853937 prefixEnd_1853937 951960784154618196661405 := by
  unfold tailWord_1853937
  simp only [CollatzResearch.WordTrace]
  refine ⟨67618637484510351076728065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45079091656340234051152043 67618637484510351076728065)
  ·
    refine ⟨50713978113382763307546049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67618637484510351076728065 50713978113382763307546049)
    ·
      refine ⟨38035483585037072480659537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50713978113382763307546049 38035483585037072480659537)
      ·
        refine ⟨28526612688777804360494653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38035483585037072480659537 28526612688777804360494653)
        ·
          refine ⟨10697479758291676635185495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28526612688777804360494653 10697479758291676635185495)
          ·
            refine ⟨16046219637437514952778243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10697479758291676635185495 16046219637437514952778243)
            ·
              refine ⟨24069329456156272429167365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16046219637437514952778243 24069329456156272429167365)
              ·
                refine ⟨4512999273029301080468881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24069329456156272429167365 4512999273029301080468881)
                ·
                  refine ⟨3384749454771975810351661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4512999273029301080468881 3384749454771975810351661)
                  ·
                    refine ⟨1269281045539490928881873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3384749454771975810351661 1269281045539490928881873)
                    ·
                      refine ⟨951960784154618196661405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269281045539490928881873 951960784154618196661405)
                      ·
                        rfl

theorem cell23_1853937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_1853937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853937 prefixEnd_1853937 := by exact prefixLift 1853937
  have htrace : WordTrace (prefixWord ++ tailWord_1853937) baseStart_1853937 baseEnd_1853937 := by
    simpa [prefixWord, tailWord_1853937, baseEnd_1853937] using wordTrace_append hprefix tailTrace_1853937
  have hstable : (prefixWord ++ tailWord_1853937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853937).length < 2 ^ (prefixWord ++ tailWord_1853937).sum := by decide
  have hdescent : baseEnd_1853937 < baseStart_1853937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853938 : List Nat := [3, 2, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_1853938 : Nat := 118140960795 + 1853938 * 2 ^ 59
def prefixEnd_1853938 : Nat := 4983230072969 + 3 ^ 40 * 1853938 * 2
def baseEnd_1853938 : Nat := 317320432545090897582967

theorem tailTrace_1853938 : CollatzResearch.WordTrace tailWord_1853938 prefixEnd_1853938 317320432545090897582967 := by
  unfold tailWord_1853938
  simp only [CollatzResearch.WordTrace]
  refine ⟨16904668489376682061878617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45079115971671152165009645 16904668489376682061878617)
  ·
    refine ⟨12678501367032511546408963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16904668489376682061878617 12678501367032511546408963)
    ·
      refine ⟨19017752050548767319613445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12678501367032511546408963 19017752050548767319613445)
      ·
        refine ⟨3565828509477893872427521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19017752050548767319613445 3565828509477893872427521)
        ·
          refine ⟨2674371382108420404320641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565828509477893872427521 2674371382108420404320641)
          ·
            refine ⟨2005778536581315303240481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2674371382108420404320641 2005778536581315303240481)
            ·
              refine ⟨1504333902435986477430361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005778536581315303240481 1504333902435986477430361)
              ·
                refine ⟨1128250426826989858072771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504333902435986477430361 1128250426826989858072771)
                ·
                  refine ⟨1692375640240484787109157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128250426826989858072771 1692375640240484787109157)
                  ·
                    refine ⟨317320432545090897582967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692375640240484787109157 317320432545090897582967)
                    ·
                      rfl

theorem cell23_1853938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_1853938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853938 prefixEnd_1853938 := by exact prefixLift 1853938
  have htrace : WordTrace (prefixWord ++ tailWord_1853938) baseStart_1853938 baseEnd_1853938 := by
    simpa [prefixWord, tailWord_1853938, baseEnd_1853938] using wordTrace_append hprefix tailTrace_1853938
  have hstable : (prefixWord ++ tailWord_1853938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853938).length < 2 ^ (prefixWord ++ tailWord_1853938).sum := by decide
  have hdescent : baseEnd_1853938 < baseStart_1853938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853944 : List Nat := [2, 1, 2, 1, 1, 4, 3, 4, 1, 1, 3]
def baseStart_1853944 : Nat := 118140960795 + 1853944 * 2 ^ 59
def prefixEnd_1853944 : Nat := 4983230072969 + 3 ^ 40 * 1853944 * 2
def baseEnd_1853944 : Nat := 951964378519199669273873

theorem tailTrace_1853944 : CollatzResearch.WordTrace tailWord_1853944 prefixEnd_1853944 951964378519199669273873 := by
  unfold tailWord_1853944
  simp only [CollatzResearch.WordTrace]
  refine ⟨33809446397742495636116443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45079261863656660848155257 33809446397742495636116443)
  ·
    refine ⟨50714169596613743454174665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33809446397742495636116443 50714169596613743454174665)
    ·
      refine ⟨38035627197460307590630999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50714169596613743454174665 38035627197460307590630999)
      ·
        refine ⟨57053440796190461385946499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38035627197460307590630999 57053440796190461385946499)
        ·
          refine ⟨85580161194285692078919749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57053440796190461385946499 85580161194285692078919749)
          ·
            refine ⟨16046280223928567264797453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85580161194285692078919749 16046280223928567264797453)
            ·
              refine ⟨6017355083973212724299045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16046280223928567264797453 6017355083973212724299045)
              ·
                refine ⟨1128254078244977385806071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6017355083973212724299045 1128254078244977385806071)
                ·
                  refine ⟨1692381117367466078709107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128254078244977385806071 1692381117367466078709107)
                  ·
                    refine ⟨2538571676051199118063661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1692381117367466078709107 2538571676051199118063661)
                    ·
                      refine ⟨951964378519199669273873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2538571676051199118063661 951964378519199669273873)
                      ·
                        rfl

theorem cell23_1853944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_1853944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853944 prefixEnd_1853944 := by exact prefixLift 1853944
  have htrace : WordTrace (prefixWord ++ tailWord_1853944) baseStart_1853944 baseEnd_1853944 := by
    simpa [prefixWord, tailWord_1853944, baseEnd_1853944] using wordTrace_append hprefix tailTrace_1853944
  have hstable : (prefixWord ++ tailWord_1853944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853944).length < 2 ^ (prefixWord ++ tailWord_1853944).sum := by decide
  have hdescent : baseEnd_1853944 < baseStart_1853944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853960 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 6, 4]
def baseStart_1853960 : Nat := 118140960795 + 1853960 * 2 ^ 59
def prefixEnd_1853960 : Nat := 4983230072969 + 3 ^ 40 * 1853960 * 2
def baseEnd_1853960 : Nat := 317324198069890535557933

theorem tailTrace_1853960 : CollatzResearch.WordTrace tailWord_1853960 prefixEnd_1853960 317324198069890535557933 := by
  unfold tailWord_1853960
  simp only [CollatzResearch.WordTrace]
  refine ⟨33809738181713513002407667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45079650908951350669876889 33809738181713513002407667)
  ·
    refine ⟨50714607272570269503611501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33809738181713513002407667 50714607272570269503611501)
    ·
      refine ⟨19017977727213851063854313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50714607272570269503611501 19017977727213851063854313)
      ·
        refine ⟨14263483295410388297890735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19017977727213851063854313 14263483295410388297890735)
        ·
          refine ⟨21395224943115582446836103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14263483295410388297890735 21395224943115582446836103)
          ·
            refine ⟨32092837414673373670254155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21395224943115582446836103 32092837414673373670254155)
            ·
              refine ⟨48139256122010060505381233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32092837414673373670254155 48139256122010060505381233)
              ·
                refine ⟨36104442091507545379035925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48139256122010060505381233 36104442091507545379035925)
                ·
                  refine ⟨1692395723039416189642309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36104442091507545379035925 1692395723039416189642309)
                  ·
                    refine ⟨317324198069890535557933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692395723039416189642309 317324198069890535557933)
                    ·
                      rfl

theorem cell23_1853960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_1853960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853960 prefixEnd_1853960 := by exact prefixLift 1853960
  have htrace : WordTrace (prefixWord ++ tailWord_1853960) baseStart_1853960 baseEnd_1853960 := by
    simpa [prefixWord, tailWord_1853960, baseEnd_1853960] using wordTrace_append hprefix tailTrace_1853960
  have hstable : (prefixWord ++ tailWord_1853960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853960).length < 2 ^ (prefixWord ++ tailWord_1853960).sum := by decide
  have hdescent : baseEnd_1853960 < baseStart_1853960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853967 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 5, 2, 2]
def baseStart_1853967 : Nat := 118140960795 + 1853967 * 2 ^ 59
def prefixEnd_1853967 : Nat := 4983230072969 + 3 ^ 40 * 1853967 * 2
def baseEnd_1853967 : Nat := 951976188574253079286267

theorem tailTrace_1853967 : CollatzResearch.WordTrace tailWord_1853967 prefixEnd_1853967 951976188574253079286267 := by
  unfold tailWord_1853967
  simp only [CollatzResearch.WordTrace]
  refine ⟨67619731674401666200320155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45079821116267777466880103 67619731674401666200320155)
  ·
    refine ⟨101429597511602499300480233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67619731674401666200320155 101429597511602499300480233)
    ·
      refine ⟨76072198133701874475360175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101429597511602499300480233 76072198133701874475360175)
      ·
        refine ⟨114108297200552811713040263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76072198133701874475360175 114108297200552811713040263)
        ·
          refine ⟨171162445800829217569560395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114108297200552811713040263 171162445800829217569560395)
          ·
            refine ⟨256743668701243826354340593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171162445800829217569560395 256743668701243826354340593)
            ·
              refine ⟨192557751525932869765755445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256743668701243826354340593 192557751525932869765755445)
              ·
                refine ⟨18052289205556206540539573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192557751525932869765755445 18052289205556206540539573)
                ·
                  refine ⟨1692402113020894363175585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18052289205556206540539573 1692402113020894363175585)
                  ·
                    refine ⟨1269301584765670772381689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1692402113020894363175585 1269301584765670772381689)
                    ·
                      refine ⟨951976188574253079286267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269301584765670772381689 951976188574253079286267)
                      ·
                        rfl

theorem cell23_1853967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 2, 2].length) (baseStart_1853967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853967 prefixEnd_1853967 := by exact prefixLift 1853967
  have htrace : WordTrace (prefixWord ++ tailWord_1853967) baseStart_1853967 baseEnd_1853967 := by
    simpa [prefixWord, tailWord_1853967, baseEnd_1853967] using wordTrace_append hprefix tailTrace_1853967
  have hstable : (prefixWord ++ tailWord_1853967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853967).length < 2 ^ (prefixWord ++ tailWord_1853967).sum := by decide
  have hdescent : baseEnd_1853967 < baseStart_1853967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853984 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1853984 : Nat := 118140960795 + 1853984 * 2 ^ 59
def prefixEnd_1853984 : Nat := 4983230072969 + 3 ^ 40 * 1853984 * 2
def baseEnd_1853984 : Nat := 951984917745379512773689

theorem tailTrace_1853984 : CollatzResearch.WordTrace tailWord_1853984 prefixEnd_1853984 951984917745379512773689 := by
  unfold tailWord_1853984
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810175857670039051844503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45080234476893385402459337 33810175857670039051844503)
  ·
    refine ⟨50715263786505058577766755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33810175857670039051844503 50715263786505058577766755)
    ·
      refine ⟨76072895679757587866650133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50715263786505058577766755 76072895679757587866650133)
      ·
        refine ⟨3565916984988636931249225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76072895679757587866650133 3565916984988636931249225)
        ·
          refine ⟨2674437738741477698436919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565916984988636931249225 2674437738741477698436919)
          ·
            refine ⟨4011656608112216547655379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674437738741477698436919 4011656608112216547655379)
            ·
              refine ⟨6017484912168324821483069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011656608112216547655379 6017484912168324821483069)
              ·
                refine ⟨2256556842063121808056151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6017484912168324821483069 2256556842063121808056151)
                ·
                  refine ⟨3384835263094682712084227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256556842063121808056151 3384835263094682712084227)
                  ·
                    refine ⟨5077252894642024068126341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3384835263094682712084227 5077252894642024068126341)
                    ·
                      refine ⟨951984917745379512773689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5077252894642024068126341 951984917745379512773689)
                      ·
                        rfl

theorem cell23_1853984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1853984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853984 prefixEnd_1853984 := by exact prefixLift 1853984
  have htrace : WordTrace (prefixWord ++ tailWord_1853984) baseStart_1853984 baseEnd_1853984 := by
    simpa [prefixWord, tailWord_1853984, baseEnd_1853984] using wordTrace_append hprefix tailTrace_1853984
  have hstable : (prefixWord ++ tailWord_1853984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853984).length < 2 ^ (prefixWord ++ tailWord_1853984).sum := by decide
  have hdescent : baseEnd_1853984 < baseStart_1853984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853994 : List Nat := [3, 1, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1853994 : Nat := 118140960795 + 1853994 * 2 ^ 59
def prefixEnd_1853994 : Nat := 4983230072969 + 3 ^ 40 * 1853994 * 2
def baseEnd_1853994 : Nat := 317330017517308157882881

theorem tailTrace_1853994 : CollatzResearch.WordTrace tailWord_1853994 prefixEnd_1853994 317330017517308157882881 := by
  unfold tailWord_1853994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16905179111325962452888259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45080477630202566541035357 16905179111325962452888259)
  ·
    refine ⟨25357768666988943679332389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16905179111325962452888259 25357768666988943679332389)
    ·
      refine ⟨4754581625060426939874823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25357768666988943679332389 4754581625060426939874823)
      ·
        refine ⟨7131872437590640409812235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4754581625060426939874823 7131872437590640409812235)
        ·
          refine ⟨10697808656385960614718353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7131872437590640409812235 10697808656385960614718353)
          ·
            refine ⟨8023356492289470461038765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10697808656385960614718353 8023356492289470461038765)
            ·
              refine ⟨3008758684608551422889537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8023356492289470461038765 3008758684608551422889537)
              ·
                refine ⟨2256569013456413567167153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008758684608551422889537 2256569013456413567167153)
                ·
                  refine ⟨1692426760092310175375365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2256569013456413567167153 1692426760092310175375365)
                  ·
                    refine ⟨317330017517308157882881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692426760092310175375365 317330017517308157882881)
                    ·
                      rfl

theorem cell23_1853994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1853994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1853994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1853994 prefixEnd_1853994 := by exact prefixLift 1853994
  have htrace : WordTrace (prefixWord ++ tailWord_1853994) baseStart_1853994 baseEnd_1853994 := by
    simpa [prefixWord, tailWord_1853994, baseEnd_1853994] using wordTrace_append hprefix tailTrace_1853994
  have hstable : (prefixWord ++ tailWord_1853994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853994).length < 2 ^ (prefixWord ++ tailWord_1853994).sum := by decide
  have hdescent : baseEnd_1853994 < baseStart_1853994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854000 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3]
def baseStart_1854000 : Nat := 118140960795 + 1854000 * 2 ^ 59
def prefixEnd_1854000 : Nat := 4983230072969 + 3 ^ 40 * 1854000 * 2
def baseEnd_1854000 : Nat := 951993133435851450173615

theorem tailTrace_1854000 : CollatzResearch.WordTrace tailWord_1854000 prefixEnd_1854000 951993133435851450173615 := by
  unfold tailWord_1854000
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810467641641056418135727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45080623522188075224180969 33810467641641056418135727)
  ·
    refine ⟨50715701462461584627203591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33810467641641056418135727 50715701462461584627203591)
    ·
      refine ⟨76073552193692376940805387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50715701462461584627203591 76073552193692376940805387)
      ·
        refine ⟨114110328290538565411208081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76073552193692376940805387 114110328290538565411208081)
        ·
          refine ⟨85582746217903924058406061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114110328290538565411208081 85582746217903924058406061)
          ·
            refine ⟨32093529831713971521902273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85582746217903924058406061 32093529831713971521902273)
            ·
              refine ⟨24070147373785478641426705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32093529831713971521902273 24070147373785478641426705)
              ·
                refine ⟨18052610530339108981070029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24070147373785478641426705 18052610530339108981070029)
                ·
                  refine ⟨6769728948877165867901261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18052610530339108981070029 6769728948877165867901261)
                  ·
                    refine ⟨2538648355828937200462973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6769728948877165867901261 2538648355828937200462973)
                    ·
                      refine ⟨951993133435851450173615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2538648355828937200462973 951993133435851450173615)
                      ·
                        rfl

theorem cell23_1854000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_1854000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854000 prefixEnd_1854000 := by exact prefixLift 1854000
  have htrace : WordTrace (prefixWord ++ tailWord_1854000) baseStart_1854000 baseEnd_1854000 := by
    simpa [prefixWord, tailWord_1854000, baseEnd_1854000] using wordTrace_append hprefix tailTrace_1854000
  have hstable : (prefixWord ++ tailWord_1854000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854000).length < 2 ^ (prefixWord ++ tailWord_1854000).sum := by decide
  have hdescent : baseEnd_1854000 < baseStart_1854000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854001 : List Nat := [1, 2, 2, 3, 1, 1, 4, 4, 1, 2, 2]
def baseStart_1854001 : Nat := 118140960795 + 1854001 * 2 ^ 59
def prefixEnd_1854001 : Nat := 4983230072969 + 3 ^ 40 * 1854001 * 2
def baseEnd_1854001 : Nat := 951993646916505946261111

theorem tailTrace_1854001 : CollatzResearch.WordTrace tailWord_1854001 prefixEnd_1854001 951993646916505946261111 := by
  unfold tailWord_1854001
  simp only [CollatzResearch.WordTrace]
  refine ⟨67620971756278490007057857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45080647837518993338038571 67620971756278490007057857)
  ·
    refine ⟨50715728817208867505293393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67620971756278490007057857 50715728817208867505293393)
    ·
      refine ⟨38036796612906650628970045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50715728817208867505293393 38036796612906650628970045)
      ·
        refine ⟨14263798729839993985863767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38036796612906650628970045 14263798729839993985863767)
        ·
          refine ⟨21395698094759990978795651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14263798729839993985863767 21395698094759990978795651)
          ·
            refine ⟨32093547142139986468193477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21395698094759990978795651 32093547142139986468193477)
            ·
              refine ⟨6017540089151247462786277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32093547142139986468193477 6017540089151247462786277)
              ·
                refine ⟨1128288766715858899272427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6017540089151247462786277 1128288766715858899272427)
                ·
                  refine ⟨1692433150073788348908641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128288766715858899272427 1692433150073788348908641)
                  ·
                    refine ⟨1269324862555341261681481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1692433150073788348908641 1269324862555341261681481)
                    ·
                      refine ⟨951993646916505946261111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269324862555341261681481 951993646916505946261111)
                      ·
                        rfl

theorem cell23_1854001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_1854001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854001 prefixEnd_1854001 := by exact prefixLift 1854001
  have htrace : WordTrace (prefixWord ++ tailWord_1854001) baseStart_1854001 baseEnd_1854001 := by
    simpa [prefixWord, tailWord_1854001, baseEnd_1854001] using wordTrace_append hprefix tailTrace_1854001
  have hstable : (prefixWord ++ tailWord_1854001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854001).length < 2 ^ (prefixWord ++ tailWord_1854001).sum := by decide
  have hdescent : baseEnd_1854001 < baseStart_1854001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854014 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1854014 : Nat := 118140960795 + 1854014 * 2 ^ 59
def prefixEnd_1854014 : Nat := 4983230072969 + 3 ^ 40 * 1854014 * 2
def baseEnd_1854014 : Nat := 952000322165014395398551

theorem tailTrace_1854014 : CollatzResearch.WordTrace tailWord_1854014 prefixEnd_1854014 952000322165014395398551 := by
  unfold tailWord_1854014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8452680738153924153410137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45080963936820928818187397 8452680738153924153410137)
  ·
    refine ⟨6339510553615443115057603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8452680738153924153410137 6339510553615443115057603)
    ·
      refine ⟨9509265830423164672586405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6339510553615443115057603 9509265830423164672586405)
      ·
        refine ⟨1782987343204343376109951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9509265830423164672586405 1782987343204343376109951)
        ·
          refine ⟨2674481014806515064164927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782987343204343376109951 2674481014806515064164927)
          ·
            refine ⟨4011721522209772596247391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674481014806515064164927 4011721522209772596247391)
            ·
              refine ⟨6017582283314658894371087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011721522209772596247391 6017582283314658894371087)
              ·
                refine ⟨9026373424971988341556631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6017582283314658894371087 9026373424971988341556631)
                ·
                  refine ⟨13539560137457982512334947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9026373424971988341556631 13539560137457982512334947)
                  ·
                    refine ⟨20309340206186973768502421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13539560137457982512334947 20309340206186973768502421)
                    ·
                      refine ⟨952000322165014395398551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20309340206186973768502421 952000322165014395398551)
                      ·
                        rfl

theorem cell23_1854014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1854014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854014 prefixEnd_1854014 := by exact prefixLift 1854014
  have htrace : WordTrace (prefixWord ++ tailWord_1854014) baseStart_1854014 baseEnd_1854014 := by
    simpa [prefixWord, tailWord_1854014, baseEnd_1854014] using wordTrace_append hprefix tailTrace_1854014
  have hstable : (prefixWord ++ tailWord_1854014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854014).length < 2 ^ (prefixWord ++ tailWord_1854014).sum := by decide
  have hdescent : baseEnd_1854014 < baseStart_1854014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854027 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 3, 3, 2]
def baseStart_1854027 : Nat := 118140960795 + 1854027 * 2 ^ 59
def prefixEnd_1854027 : Nat := 4983230072969 + 3 ^ 40 * 1854027 * 2
def baseEnd_1854027 : Nat := 952006997413522844535991

theorem tailTrace_1854027 : CollatzResearch.WordTrace tailWord_1854027 prefixEnd_1854027 952006997413522844535991 := by
  unfold tailWord_1854027
  simp only [CollatzResearch.WordTrace]
  refine ⟨67621920054184296447504335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45081280036122864298336223 67621920054184296447504335)
  ·
    refine ⟨101432880081276444671256503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67621920054184296447504335 101432880081276444671256503)
    ·
      refine ⟨152149320121914667006884755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101432880081276444671256503 152149320121914667006884755)
      ·
        refine ⟨228223980182872000510327133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152149320121914667006884755 228223980182872000510327133)
        ·
          refine ⟨85583992568577000191372675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228223980182872000510327133 85583992568577000191372675)
          ·
            refine ⟨128375988852865500287059013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85583992568577000191372675 128375988852865500287059013)
            ·
              refine ⟨24070497909912281303823565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128375988852865500287059013 24070497909912281303823565)
              ·
                refine ⟨9026436716217105488933837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24070497909912281303823565 9026436716217105488933837)
                ·
                  refine ⟨3384913768581414558350189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9026436716217105488933837 3384913768581414558350189)
                  ·
                    refine ⟨1269342663218030459381321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3384913768581414558350189 1269342663218030459381321)
                    ·
                      refine ⟨952006997413522844535991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269342663218030459381321 952006997413522844535991)
                      ·
                        rfl

theorem cell23_1854027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3, 2].length) (baseStart_1854027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854027 prefixEnd_1854027 := by exact prefixLift 1854027
  have htrace : WordTrace (prefixWord ++ tailWord_1854027) baseStart_1854027 baseEnd_1854027 := by
    simpa [prefixWord, tailWord_1854027, baseEnd_1854027] using wordTrace_append hprefix tailTrace_1854027
  have hstable : (prefixWord ++ tailWord_1854027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854027).length < 2 ^ (prefixWord ++ tailWord_1854027).sum := by decide
  have hdescent : baseEnd_1854027 < baseStart_1854027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854030 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1854030 : Nat := 118140960795 + 1854030 * 2 ^ 59
def prefixEnd_1854030 : Nat := 4983230072969 + 3 ^ 40 * 1854030 * 2
def baseEnd_1854030 : Nat := 952008537855486332798477

theorem tailTrace_1854030 : CollatzResearch.WordTrace tailWord_1854030 prefixEnd_1854030 952008537855486332798477 := by
  unfold tailWord_1854030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8452753684146678494982943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45081352982115618639909029 8452753684146678494982943)
  ·
    refine ⟨12679130526220017742474415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8452753684146678494982943 12679130526220017742474415)
    ·
      refine ⟨19018695789330026613711623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12679130526220017742474415 19018695789330026613711623)
      ·
        refine ⟨28528043683995039920567435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19018695789330026613711623 28528043683995039920567435)
        ·
          refine ⟨42792065525992559880851153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28528043683995039920567435 42792065525992559880851153)
          ·
            refine ⟨32094049144494419910638365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42792065525992559880851153 32094049144494419910638365)
            ·
              refine ⟨12035268429185407466489387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32094049144494419910638365 12035268429185407466489387)
              ·
                refine ⟨18052902643778111199734081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12035268429185407466489387 18052902643778111199734081)
                ·
                  refine ⟨13539676982833583399800561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18052902643778111199734081 13539676982833583399800561)
                  ·
                    refine ⟨10154757737125187549850421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13539676982833583399800561 10154757737125187549850421)
                    ·
                      refine ⟨952008537855486332798477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10154757737125187549850421 952008537855486332798477)
                      ·
                        rfl

theorem cell23_1854030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1854030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854030 prefixEnd_1854030 := by exact prefixLift 1854030
  have htrace : WordTrace (prefixWord ++ tailWord_1854030) baseStart_1854030 baseEnd_1854030 := by
    simpa [prefixWord, tailWord_1854030, baseEnd_1854030] using wordTrace_append hprefix tailTrace_1854030
  have hstable : (prefixWord ++ tailWord_1854030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854030).length < 2 ^ (prefixWord ++ tailWord_1854030).sum := by decide
  have hdescent : baseEnd_1854030 < baseStart_1854030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854108 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_1854108 : Nat := 118140960795 + 1854108 * 2 ^ 59
def prefixEnd_1854108 : Nat := 4983230072969 + 3 ^ 40 * 1854108 * 2
def baseEnd_1854108 : Nat := 952048589346537027623119

theorem tailTrace_1854108 : CollatzResearch.WordTrace tailWord_1854108 prefixEnd_1854108 952048589346537027623119 := by
  unfold tailWord_1854108
  simp only [CollatzResearch.WordTrace]
  refine ⟨33812437183445423640601489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45083249577927231520801985 33812437183445423640601489)
  ·
    refine ⟨25359327887584067730451117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33812437183445423640601489 25359327887584067730451117)
    ·
      refine ⟨9509747957844025398919169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25359327887584067730451117 9509747957844025398919169)
      ·
        refine ⟨7132310968383019049189377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9509747957844025398919169 7132310968383019049189377)
        ·
          refine ⟨5349233226287264286892033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7132310968383019049189377 5349233226287264286892033)
          ·
            refine ⟨4011924919715448215169025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5349233226287264286892033 4011924919715448215169025)
            ·
              refine ⟨3008943689786586161376769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011924919715448215169025 3008943689786586161376769)
              ·
                refine ⟨2256707767339939621032577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008943689786586161376769 2256707767339939621032577)
                ·
                  refine ⟨1692530825504954715774433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2256707767339939621032577 1692530825504954715774433)
                  ·
                    refine ⟨1269398119128716036830825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1692530825504954715774433 1269398119128716036830825)
                    ·
                      refine ⟨952048589346537027623119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269398119128716036830825 952048589346537027623119)
                      ·
                        rfl

theorem cell23_1854108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_1854108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854108 prefixEnd_1854108 := by exact prefixLift 1854108
  have htrace : WordTrace (prefixWord ++ tailWord_1854108) baseStart_1854108 baseEnd_1854108 := by
    simpa [prefixWord, tailWord_1854108, baseEnd_1854108] using wordTrace_append hprefix tailTrace_1854108
  have hstable : (prefixWord ++ tailWord_1854108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854108).length < 2 ^ (prefixWord ++ tailWord_1854108).sum := by decide
  have hdescent : baseEnd_1854108 < baseStart_1854108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854144 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 2, 5]
def baseStart_1854144 : Nat := 118140960795 + 1854144 * 2 ^ 59
def prefixEnd_1854144 : Nat := 4983230072969 + 3 ^ 40 * 1854144 * 2
def baseEnd_1854144 : Nat := 317355691550032962257651

theorem tailTrace_1854144 : CollatzResearch.WordTrace tailWord_1854144 prefixEnd_1854144 317355691550032962257651 := by
  unfold tailWord_1854144
  simp only [CollatzResearch.WordTrace]
  refine ⟨33813093697380212714756743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45084124929840283619675657 33813093697380212714756743)
  ·
    refine ⟨50719640546070319072135115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33813093697380212714756743 50719640546070319072135115)
    ·
      refine ⟨76079460819105478608202673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50719640546070319072135115 76079460819105478608202673)
      ·
        refine ⟨57059595614329108956152005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76079460819105478608202673 57059595614329108956152005)
        ·
          refine ⟨10698674177686707929278501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57059595614329108956152005 10698674177686707929278501)
          ·
            refine ⟨2006001408316257736739719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10698674177686707929278501 2006001408316257736739719)
            ·
              refine ⟨3009002112474386605109579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006001408316257736739719 3009002112474386605109579)
              ·
                refine ⟨4513503168711579907664369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009002112474386605109579 4513503168711579907664369)
                ·
                  refine ⟨3385127376533684930748277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4513503168711579907664369 3385127376533684930748277)
                  ·
                    refine ⟨317355691550032962257651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3385127376533684930748277 317355691550032962257651)
                    ·
                      rfl

theorem cell23_1854144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_1854144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854144 prefixEnd_1854144 := by exact prefixLift 1854144
  have htrace : WordTrace (prefixWord ++ tailWord_1854144) baseStart_1854144 baseEnd_1854144 := by
    simpa [prefixWord, tailWord_1854144, baseEnd_1854144] using wordTrace_append hprefix tailTrace_1854144
  have hstable : (prefixWord ++ tailWord_1854144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854144).length < 2 ^ (prefixWord ++ tailWord_1854144).sum := by decide
  have hdescent : baseEnd_1854144 < baseStart_1854144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854281 : List Nat := [1, 2, 1, 1, 2, 6, 2, 2, 2, 4]
def baseStart_1854281 : Nat := 118140960795 + 1854281 * 2 ^ 59
def prefixEnd_1854281 : Nat := 4983230072969 + 3 ^ 40 * 1854281 * 2
def baseEnd_1854281 : Nat := 317379140499921616919941

theorem tailTrace_1854281 : CollatzResearch.WordTrace tailWord_1854281 prefixEnd_1854281 317379140499921616919941 := by
  unfold tailWord_1854281
  simp only [CollatzResearch.WordTrace]
  refine ⟨67631184195264097827250697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45087456130176065218167131 67631184195264097827250697)
  ·
    refine ⟨50723388146448073370438023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67631184195264097827250697 50723388146448073370438023)
    ·
      refine ⟨76085082219672110055657035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50723388146448073370438023 76085082219672110055657035)
      ·
        refine ⟨114127623329508165083485553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76085082219672110055657035 114127623329508165083485553)
        ·
          refine ⟨85595717497131123812614165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114127623329508165083485553 85595717497131123812614165)
          ·
            refine ⟨4012299257678021428716289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85595717497131123812614165 4012299257678021428716289)
            ·
              refine ⟨3009224443258516071537217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012299257678021428716289 3009224443258516071537217)
              ·
                refine ⟨2256918332443887053652913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3009224443258516071537217 2256918332443887053652913)
                ·
                  refine ⟨1692688749332915290239685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2256918332443887053652913 1692688749332915290239685)
                  ·
                    refine ⟨317379140499921616919941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692688749332915290239685 317379140499921616919941)
                    ·
                      rfl

theorem cell23_1854281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 4].length) (baseStart_1854281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854281 prefixEnd_1854281 := by exact prefixLift 1854281
  have htrace : WordTrace (prefixWord ++ tailWord_1854281) baseStart_1854281 baseEnd_1854281 := by
    simpa [prefixWord, tailWord_1854281, baseEnd_1854281] using wordTrace_append hprefix tailTrace_1854281
  have hstable : (prefixWord ++ tailWord_1854281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854281).length < 2 ^ (prefixWord ++ tailWord_1854281).sum := by decide
  have hdescent : baseEnd_1854281 < baseStart_1854281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854325 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_1854325 : Nat := 118140960795 + 1854325 * 2 ^ 59
def prefixEnd_1854325 : Nat := 4983230072969 + 3 ^ 40 * 1854325 * 2
def baseEnd_1854325 : Nat := 952160014648562678609621

theorem tailTrace_1854325 : CollatzResearch.WordTrace tailWord_1854325 prefixEnd_1854325 952160014648562678609621 := by
  unfold tailWord_1854325
  simp only [CollatzResearch.WordTrace]
  refine ⟨67632789007104693341852429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45088526004736462227901619 67632789007104693341852429)
  ·
    refine ⟨25362295877664260003194661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67632789007104693341852429 25362295877664260003194661)
    ·
      refine ⟨4755430477062048750598999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25362295877664260003194661 4755430477062048750598999)
      ·
        refine ⟨7133145715593073125898499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4755430477062048750598999 7133145715593073125898499)
        ·
          refine ⟨10699718573389609688847749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7133145715593073125898499 10699718573389609688847749)
          ·
            refine ⟨2006197232510551816658953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10699718573389609688847749 2006197232510551816658953)
            ·
              refine ⟨1504647924382913862494215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006197232510551816658953 1504647924382913862494215)
              ·
                refine ⟨2256971886574370793741323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504647924382913862494215 2256971886574370793741323)
                ·
                  refine ⟨3385457829861556190611985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256971886574370793741323 3385457829861556190611985)
                  ·
                    refine ⟨2539093372396167142958989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385457829861556190611985 2539093372396167142958989)
                    ·
                      refine ⟨952160014648562678609621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539093372396167142958989 952160014648562678609621)
                      ·
                        rfl

theorem cell23_1854325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_1854325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854325 prefixEnd_1854325 := by exact prefixLift 1854325
  have htrace : WordTrace (prefixWord ++ tailWord_1854325) baseStart_1854325 baseEnd_1854325 := by
    simpa [prefixWord, tailWord_1854325, baseEnd_1854325] using wordTrace_append hprefix tailTrace_1854325
  have hstable : (prefixWord ++ tailWord_1854325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854325).length < 2 ^ (prefixWord ++ tailWord_1854325).sum := by decide
  have hdescent : baseEnd_1854325 < baseStart_1854325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854406 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1854406 : Nat := 118140960795 + 1854406 * 2 ^ 59
def prefixEnd_1854406 : Nat := 4983230072969 + 3 ^ 40 * 1854406 * 2
def baseEnd_1854406 : Nat := 952201606581576861696749

theorem tailTrace_1854406 : CollatzResearch.WordTrace tailWord_1854406 prefixEnd_1854406 952201606581576861696749 := by
  unfold tailWord_1854406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113616978744101380485971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45090495546540829450367381 2113616978744101380485971)
  ·
    refine ⟨3170425468116152070728957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2113616978744101380485971 3170425468116152070728957)
    ·
      refine ⟨1188909550543557026523359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3170425468116152070728957 1188909550543557026523359)
      ·
        refine ⟨1783364325815335539785039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188909550543557026523359 1783364325815335539785039)
        ·
          refine ⟨2675046488723003309677559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783364325815335539785039 2675046488723003309677559)
          ·
            refine ⟨4012569733084504964516339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675046488723003309677559 4012569733084504964516339)
            ·
              refine ⟨6018854599626757446774509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012569733084504964516339 6018854599626757446774509)
              ·
                refine ⟨2257070474860034042540441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6018854599626757446774509 2257070474860034042540441)
                ·
                  refine ⟨1692802856145025531905331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257070474860034042540441 1692802856145025531905331)
                  ·
                    refine ⟨2539204284217538297857997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1692802856145025531905331 2539204284217538297857997)
                    ·
                      refine ⟨952201606581576861696749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539204284217538297857997 952201606581576861696749)
                      ·
                        rfl

theorem cell23_1854406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1854406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854406 prefixEnd_1854406 := by exact prefixLift 1854406
  have htrace : WordTrace (prefixWord ++ tailWord_1854406) baseStart_1854406 baseEnd_1854406 := by
    simpa [prefixWord, tailWord_1854406, baseEnd_1854406] using wordTrace_append hprefix tailTrace_1854406
  have hstable : (prefixWord ++ tailWord_1854406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854406).length < 2 ^ (prefixWord ++ tailWord_1854406).sum := by decide
  have hdescent : baseEnd_1854406 < baseStart_1854406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854461 : List Nat := [1, 4, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_1854461 : Nat := 118140960795 + 1854461 * 2 ^ 59
def prefixEnd_1854461 : Nat := 4983230072969 + 3 ^ 40 * 1854461 * 2
def baseEnd_1854461 : Nat := 317409949339191382169665

theorem tailTrace_1854461 : CollatzResearch.WordTrace tailWord_1854461 prefixEnd_1854461 317409949339191382169665 := by
  unfold tailWord_1854461
  simp only [CollatzResearch.WordTrace]
  refine ⟨67637749334611988568803237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45091832889741325712535491 67637749334611988568803237)
  ·
    refine ⟨12682078000239747856650607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67637749334611988568803237 12682078000239747856650607)
    ·
      refine ⟨19023117000359621784975911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12682078000239747856650607 19023117000359621784975911)
      ·
        refine ⟨28534675500539432677463867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19023117000359621784975911 28534675500539432677463867)
        ·
          refine ⟨42802013250809149016195801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28534675500539432677463867 42802013250809149016195801)
          ·
            refine ⟨32101509938106861762146851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42802013250809149016195801 32101509938106861762146851)
            ·
              refine ⟨48152264907160292643220277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32101509938106861762146851 48152264907160292643220277)
              ·
                refine ⟨4514274835046277435301901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48152264907160292643220277 4514274835046277435301901)
                ·
                  refine ⟨1692853063142354038238213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4514274835046277435301901 1692853063142354038238213)
                  ·
                    refine ⟨317409949339191382169665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692853063142354038238213 317409949339191382169665)
                    ·
                      rfl

theorem cell23_1854461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_1854461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854461 prefixEnd_1854461 := by exact prefixLift 1854461
  have htrace : WordTrace (prefixWord ++ tailWord_1854461) baseStart_1854461 baseEnd_1854461 := by
    simpa [prefixWord, tailWord_1854461, baseEnd_1854461] using wordTrace_append hprefix tailTrace_1854461
  have hstable : (prefixWord ++ tailWord_1854461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854461).length < 2 ^ (prefixWord ++ tailWord_1854461).sum := by decide
  have hdescent : baseEnd_1854461 < baseStart_1854461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854471 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1854471 : Nat := 118140960795 + 1854471 * 2 ^ 59
def prefixEnd_1854471 : Nat := 4983230072969 + 3 ^ 40 * 1854471 * 2
def baseEnd_1854471 : Nat := 952234982824119107383949

theorem tailTrace_1854471 : CollatzResearch.WordTrace tailWord_1854471 prefixEnd_1854471 952234982824119107383949 := by
  unfold tailWord_1854471
  simp only [CollatzResearch.WordTrace]
  refine ⟨67638114064575760276667267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45092076043050506851111511 67638114064575760276667267)
  ·
    refine ⟨101457171096863640415000901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67638114064575760276667267 101457171096863640415000901)
    ·
      refine ⟨19023219580661932577812669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101457171096863640415000901 19023219580661932577812669)
      ·
        refine ⟨7133707342748224716679751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19023219580661932577812669 7133707342748224716679751)
        ·
          refine ⟨10700561014122337075019627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7133707342748224716679751 10700561014122337075019627)
          ·
            refine ⟨16050841521183505612529441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10700561014122337075019627 16050841521183505612529441)
            ·
              refine ⟨12038131140887629209397081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16050841521183505612529441 12038131140887629209397081)
              ·
                refine ⟨9028598355665721907047811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12038131140887629209397081 9028598355665721907047811)
                ·
                  refine ⟨13542897533498582860571717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9028598355665721907047811 13542897533498582860571717)
                  ·
                    refine ⟨2539293287530984286357197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13542897533498582860571717 2539293287530984286357197)
                    ·
                      refine ⟨952234982824119107383949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539293287530984286357197 952234982824119107383949)
                      ·
                        rfl

theorem cell23_1854471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1854471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854471 prefixEnd_1854471 := by exact prefixLift 1854471
  have htrace : WordTrace (prefixWord ++ tailWord_1854471) baseStart_1854471 baseEnd_1854471 := by
    simpa [prefixWord, tailWord_1854471, baseEnd_1854471] using wordTrace_append hprefix tailTrace_1854471
  have hstable : (prefixWord ++ tailWord_1854471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854471).length < 2 ^ (prefixWord ++ tailWord_1854471).sum := by decide
  have hdescent : baseEnd_1854471 < baseStart_1854471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854478 : List Nat := [4, 1, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_1854478 : Nat := 118140960795 + 1854478 * 2 ^ 59
def prefixEnd_1854478 : Nat := 4983230072969 + 3 ^ 40 * 1854478 * 2
def baseEnd_1854478 : Nat := 317412859062900193332139

theorem tailTrace_1854478 : CollatzResearch.WordTrace tailWord_1854478 prefixEnd_1854478 317412859062900193332139 := by
  unfold tailWord_1854478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454796171943800059021511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45092246250366933648114725 8454796171943800059021511)
  ·
    refine ⟨12682194257915700088532267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8454796171943800059021511 12682194257915700088532267)
    ·
      refine ⟨19023291386873550132798401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12682194257915700088532267 19023291386873550132798401)
      ·
        refine ⟨14267468540155162599598801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19023291386873550132798401 14267468540155162599598801)
        ·
          refine ⟨10700601405116371949699101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14267468540155162599598801 10700601405116371949699101)
          ·
            refine ⟨4012725526918639481137163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10700601405116371949699101 4012725526918639481137163)
            ·
              refine ⟨6019088290377959221705745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012725526918639481137163 6019088290377959221705745)
              ·
                refine ⟨4514316217783469416279309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6019088290377959221705745 4514316217783469416279309)
                ·
                  refine ⟨1692868581668801031104741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4514316217783469416279309 1692868581668801031104741)
                  ·
                    refine ⟨317412859062900193332139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692868581668801031104741 317412859062900193332139)
                    ·
                      rfl

theorem cell23_1854478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_1854478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854478 prefixEnd_1854478 := by exact prefixLift 1854478
  have htrace : WordTrace (prefixWord ++ tailWord_1854478) baseStart_1854478 baseEnd_1854478 := by
    simpa [prefixWord, tailWord_1854478, baseEnd_1854478] using wordTrace_append hprefix tailTrace_1854478
  have hstable : (prefixWord ++ tailWord_1854478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854478).length < 2 ^ (prefixWord ++ tailWord_1854478).sum := by decide
  have hdescent : baseEnd_1854478 < baseStart_1854478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854488 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1854488 : Nat := 118140960795 + 1854488 * 2 ^ 59
def prefixEnd_1854488 : Nat := 4983230072969 + 3 ^ 40 * 1854488 * 2
def baseEnd_1854488 : Nat := 952243711995245540871371

theorem tailTrace_1854488 : CollatzResearch.WordTrace tailWord_1854488 prefixEnd_1854488 952243711995245540871371 := by
  unfold tailWord_1854488
  simp only [CollatzResearch.WordTrace]
  refine ⟨33819367052757086090018059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45092489403676114786690745 33819367052757086090018059)
  ·
    refine ⟨50729050579135629135027089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33819367052757086090018059 50729050579135629135027089)
    ·
      refine ⟨38046787934351721851270317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50729050579135629135027089 38046787934351721851270317)
      ·
        refine ⟨14267545475381895694226369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38046787934351721851270317 14267545475381895694226369)
        ·
          refine ⟨10700659106536421770669777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14267545475381895694226369 10700659106536421770669777)
          ·
            refine ⟨8025494329902316328002333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10700659106536421770669777 8025494329902316328002333)
            ·
              refine ⟨3009560373713368623000875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8025494329902316328002333 3009560373713368623000875)
              ·
                refine ⟨4514340560570052934501313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009560373713368623000875 4514340560570052934501313)
                ·
                  refine ⟨3385755420427539700875985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514340560570052934501313 3385755420427539700875985)
                  ·
                    refine ⟨2539316565320654775656989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385755420427539700875985 2539316565320654775656989)
                    ·
                      refine ⟨952243711995245540871371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539316565320654775656989 952243711995245540871371)
                      ·
                        rfl

theorem cell23_1854488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1854488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854488 prefixEnd_1854488 := by exact prefixLift 1854488
  have htrace : WordTrace (prefixWord ++ tailWord_1854488) baseStart_1854488 baseEnd_1854488 := by
    simpa [prefixWord, tailWord_1854488, baseEnd_1854488] using wordTrace_append hprefix tailTrace_1854488
  have hstable : (prefixWord ++ tailWord_1854488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854488).length < 2 ^ (prefixWord ++ tailWord_1854488).sum := by decide
  have hdescent : baseEnd_1854488 < baseStart_1854488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854495 : List Nat := [1, 1, 2, 4, 1, 4, 2, 3, 1, 4]
def baseStart_1854495 : Nat := 118140960795 + 1854495 * 2 ^ 59
def prefixEnd_1854495 : Nat := 4983230072969 + 3 ^ 40 * 1854495 * 2
def baseEnd_1854495 : Nat := 317415768786609004494613

theorem tailTrace_1854495 : CollatzResearch.WordTrace tailWord_1854495 prefixEnd_1854495 317415768786609004494613 := by
  unfold tailWord_1854495
  simp only [CollatzResearch.WordTrace]
  refine ⟨67638989416488812375540939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45092659610992541583693959 67638989416488812375540939)
  ·
    refine ⟨101458484124733218563311409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67638989416488812375540939 101458484124733218563311409)
    ·
      refine ⟨76093863093549913922483557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101458484124733218563311409 76093863093549913922483557)
      ·
        refine ⟨14267599330040608860465667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76093863093549913922483557 14267599330040608860465667)
        ·
          refine ⟨21401398995060913290698501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14267599330040608860465667 21401398995060913290698501)
          ·
            refine ⟨4012762311573921242005969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21401398995060913290698501 4012762311573921242005969)
            ·
              refine ⟨3009571733680440931504477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012762311573921242005969 3009571733680440931504477)
              ·
                refine ⟨1128589400130165349314179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009571733680440931504477 1128589400130165349314179)
                ·
                  refine ⟨1692884100195248023971269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128589400130165349314179 1692884100195248023971269)
                  ·
                    refine ⟨317415768786609004494613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692884100195248023971269 317415768786609004494613)
                    ·
                      rfl

theorem cell23_1854495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 1, 4].length) (baseStart_1854495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854495 prefixEnd_1854495 := by exact prefixLift 1854495
  have htrace : WordTrace (prefixWord ++ tailWord_1854495) baseStart_1854495 baseEnd_1854495 := by
    simpa [prefixWord, tailWord_1854495, baseEnd_1854495] using wordTrace_append hprefix tailTrace_1854495
  have hstable : (prefixWord ++ tailWord_1854495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854495).length < 2 ^ (prefixWord ++ tailWord_1854495).sum := by decide
  have hdescent : baseEnd_1854495 < baseStart_1854495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854561 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1854561 : Nat := 118140960795 + 1854561 * 2 ^ 59
def prefixEnd_1854561 : Nat := 4983230072969 + 3 ^ 40 * 1854561 * 2
def baseEnd_1854561 : Nat := 952281196083023755258535

theorem tailTrace_1854561 : CollatzResearch.WordTrace tailWord_1854561 prefixEnd_1854561 952281196083023755258535 := by
  unfold tailWord_1854561
  simp only [CollatzResearch.WordTrace]
  refine ⟨67641396634249705647443537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45094264422833137098295691 67641396634249705647443537)
  ·
    refine ⟨50731047475687279235582653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67641396634249705647443537 50731047475687279235582653)
    ·
      refine ⟨19024142803382729713343495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50731047475687279235582653 19024142803382729713343495)
      ·
        refine ⟨28536214205074094570015243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19024142803382729713343495 28536214205074094570015243)
        ·
          refine ⟨42804321307611141855022865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28536214205074094570015243 42804321307611141855022865)
          ·
            refine ⟨32103240980708356391267149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42804321307611141855022865 32103240980708356391267149)
            ·
              refine ⟨12038715367765633646725181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32103240980708356391267149 12038715367765633646725181)
              ·
                refine ⟨4514518262912112617521943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12038715367765633646725181 4514518262912112617521943)
                ·
                  refine ⟨6771777394368168926282915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4514518262912112617521943 6771777394368168926282915)
                  ·
                    refine ⟨10157666091552253389424373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6771777394368168926282915 10157666091552253389424373)
                    ·
                      refine ⟨952281196083023755258535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10157666091552253389424373 952281196083023755258535)
                      ·
                        rfl

theorem cell23_1854561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1854561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854561 prefixEnd_1854561 := by exact prefixLift 1854561
  have htrace : WordTrace (prefixWord ++ tailWord_1854561) baseStart_1854561 baseEnd_1854561 := by
    simpa [prefixWord, tailWord_1854561, baseEnd_1854561] using wordTrace_append hprefix tailTrace_1854561
  have hstable : (prefixWord ++ tailWord_1854561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854561).length < 2 ^ (prefixWord ++ tailWord_1854561).sum := by decide
  have hdescent : baseEnd_1854561 < baseStart_1854561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854562 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1854562 : Nat := 118140960795 + 1854562 * 2 ^ 59
def prefixEnd_1854562 : Nat := 4983230072969 + 3 ^ 40 * 1854562 * 2
def baseEnd_1854562 : Nat := 952281709563678251346031

theorem tailTrace_1854562 : CollatzResearch.WordTrace tailWord_1854562 prefixEnd_1854562 952281709563678251346031 := by
  unfold tailWord_1854562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910358276811520704557485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45094288738164055212153293 16910358276811520704557485)
  ·
    refine ⟨6341384353804320264209057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16910358276811520704557485 6341384353804320264209057)
    ·
      refine ⟨4756038265353240198156793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6341384353804320264209057 4756038265353240198156793)
      ·
        refine ⟨3567028699014930148617595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4756038265353240198156793 3567028699014930148617595)
        ·
          refine ⟨5350543048522395222926393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567028699014930148617595 5350543048522395222926393)
          ·
            refine ⟨4012907286391796417194795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5350543048522395222926393 4012907286391796417194795)
            ·
              refine ⟨6019360929587694625792193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012907286391796417194795 6019360929587694625792193)
              ·
                refine ⟨4514520697190770969344145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6019360929587694625792193 4514520697190770969344145)
                ·
                  refine ⟨3385890522893078227008109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4514520697190770969344145 3385890522893078227008109)
                  ·
                    refine ⟨1269708946084904335128041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3385890522893078227008109 1269708946084904335128041)
                    ·
                      refine ⟨952281709563678251346031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269708946084904335128041 952281709563678251346031)
                      ·
                        rfl

theorem cell23_1854562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1854562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854562 prefixEnd_1854562 := by exact prefixLift 1854562
  have htrace : WordTrace (prefixWord ++ tailWord_1854562) baseStart_1854562 baseEnd_1854562 := by
    simpa [prefixWord, tailWord_1854562, baseEnd_1854562] using wordTrace_append hprefix tailTrace_1854562
  have hstable : (prefixWord ++ tailWord_1854562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854562).length < 2 ^ (prefixWord ++ tailWord_1854562).sum := by decide
  have hdescent : baseEnd_1854562 < baseStart_1854562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854578 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1854578 : Nat := 118140960795 + 1854578 * 2 ^ 59
def prefixEnd_1854578 : Nat := 4983230072969 + 3 ^ 40 * 1854578 * 2
def baseEnd_1854578 : Nat := 952289925254150188745957

theorem tailTrace_1854578 : CollatzResearch.WordTrace tailWord_1854578 prefixEnd_1854578 952289925254150188745957 := by
  unfold tailWord_1854578
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910504168797029387703097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45094677783458745033874925 16910504168797029387703097)
  ·
    refine ⟨12682878126597772040777323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16910504168797029387703097 12682878126597772040777323)
    ·
      refine ⟨19024317189896658061165985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12682878126597772040777323 19024317189896658061165985)
      ·
        refine ⟨14268237892422493545874489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19024317189896658061165985 14268237892422493545874489)
        ·
          refine ⟨10701178419316870159405867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14268237892422493545874489 10701178419316870159405867)
          ·
            refine ⟨16051767628975305239108801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10701178419316870159405867 16051767628975305239108801)
            ·
              refine ⟨12038825721731478929331601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16051767628975305239108801 12038825721731478929331601)
              ·
                refine ⟨9029119291298609196998701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12038825721731478929331601 9029119291298609196998701)
                ·
                  refine ⟨3385919734236978448874513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9029119291298609196998701 3385919734236978448874513)
                  ·
                    refine ⟨2539439800677733836655885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3385919734236978448874513 2539439800677733836655885)
                    ·
                      refine ⟨952289925254150188745957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539439800677733836655885 952289925254150188745957)
                      ·
                        rfl

theorem cell23_1854578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1854578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854578 prefixEnd_1854578 := by exact prefixLift 1854578
  have htrace : WordTrace (prefixWord ++ tailWord_1854578) baseStart_1854578 baseEnd_1854578 := by
    simpa [prefixWord, tailWord_1854578, baseEnd_1854578] using wordTrace_append hprefix tailTrace_1854578
  have hstable : (prefixWord ++ tailWord_1854578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854578).length < 2 ^ (prefixWord ++ tailWord_1854578).sum := by decide
  have hdescent : baseEnd_1854578 < baseStart_1854578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854585 : List Nat := [1, 2, 1, 3, 5, 1, 1, 3, 2, 4]
def baseStart_1854585 : Nat := 118140960795 + 1854585 * 2 ^ 59
def prefixEnd_1854585 : Nat := 4983230072969 + 3 ^ 40 * 1854585 * 2
def baseEnd_1854585 : Nat := 317431173206243887119475

theorem tailTrace_1854585 : CollatzResearch.WordTrace tailWord_1854585 prefixEnd_1854585 317431173206243887119475 := by
  unfold tailWord_1854585
  simp only [CollatzResearch.WordTrace]
  refine ⟨67642271986162757746317209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45094847990775171830878139 67642271986162757746317209)
  ·
    refine ⟨50731703989622068309737907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67642271986162757746317209 50731703989622068309737907)
    ·
      refine ⟨76097555984433102464606861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50731703989622068309737907 76097555984433102464606861)
      ·
        refine ⟨28536583494162413424227573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76097555984433102464606861 28536583494162413424227573)
        ·
          refine ⟨2675304702577726258521335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28536583494162413424227573 2675304702577726258521335)
          ·
            refine ⟨4012957053866589387782003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675304702577726258521335 4012957053866589387782003)
            ·
              refine ⟨6019435580799884081673005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012957053866589387782003 6019435580799884081673005)
              ·
                refine ⟨2257288342799956530627377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6019435580799884081673005 2257288342799956530627377)
                ·
                  refine ⟨1692966257099967397970533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257288342799956530627377 1692966257099967397970533)
                  ·
                    refine ⟨317431173206243887119475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1692966257099967397970533 317431173206243887119475)
                    ·
                      rfl

theorem cell23_1854585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 2, 4].length) (baseStart_1854585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854585 prefixEnd_1854585 := by exact prefixLift 1854585
  have htrace : WordTrace (prefixWord ++ tailWord_1854585) baseStart_1854585 baseEnd_1854585 := by
    simpa [prefixWord, tailWord_1854585, baseEnd_1854585] using wordTrace_append hprefix tailTrace_1854585
  have hstable : (prefixWord ++ tailWord_1854585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854585).length < 2 ^ (prefixWord ++ tailWord_1854585).sum := by decide
  have hdescent : baseEnd_1854585 < baseStart_1854585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854591 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 3]
def baseStart_1854591 : Nat := 118140960795 + 1854591 * 2 ^ 59
def prefixEnd_1854591 : Nat := 4983230072969 + 3 ^ 40 * 1854591 * 2
def baseEnd_1854591 : Nat := 952296600502658637883397

theorem tailTrace_1854591 : CollatzResearch.WordTrace tailWord_1854591 prefixEnd_1854591 952296600502658637883397 := by
  unfold tailWord_1854591
  simp only [CollatzResearch.WordTrace]
  refine ⟨67642490824141020771035627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45094993882760680514023751 67642490824141020771035627)
  ·
    refine ⟨101463736236211531156553441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67642490824141020771035627 101463736236211531156553441)
    ·
      refine ⟨76097802177158648367415081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101463736236211531156553441 76097802177158648367415081)
      ·
        refine ⟨57073351632868986275561311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76097802177158648367415081 57073351632868986275561311)
        ·
          refine ⟨85610027449303479413341967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57073351632868986275561311 85610027449303479413341967)
          ·
            refine ⟨128415041173955219120012951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85610027449303479413341967 128415041173955219120012951)
            ·
              refine ⟨192622561760932828680019427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128415041173955219120012951 192622561760932828680019427)
              ·
                refine ⟨288933842641399243020029141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192622561760932828680019427 288933842641399243020029141)
                ·
                  refine ⟨6771886936907794758281933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 288933842641399243020029141 6771886936907794758281933)
                  ·
                    refine ⟨2539457601340423034355725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6771886936907794758281933 2539457601340423034355725)
                    ·
                      refine ⟨952296600502658637883397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539457601340423034355725 952296600502658637883397)
                      ·
                        rfl

theorem cell23_1854591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_1854591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854591 prefixEnd_1854591 := by exact prefixLift 1854591
  have htrace : WordTrace (prefixWord ++ tailWord_1854591) baseStart_1854591 baseEnd_1854591 := by
    simpa [prefixWord, tailWord_1854591, baseEnd_1854591] using wordTrace_append hprefix tailTrace_1854591
  have hstable : (prefixWord ++ tailWord_1854591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854591).length < 2 ^ (prefixWord ++ tailWord_1854591).sum := by decide
  have hdescent : baseEnd_1854591 < baseStart_1854591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854608 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 4, 1, 3]
def baseStart_1854608 : Nat := 118140960795 + 1854608 * 2 ^ 59
def prefixEnd_1854608 : Nat := 4983230072969 + 3 ^ 40 * 1854608 * 2
def baseEnd_1854608 : Nat := 952305329673785071370819

theorem tailTrace_1854608 : CollatzResearch.WordTrace tailWord_1854608 prefixEnd_1854608 952305329673785071370819 := by
  unfold tailWord_1854608
  simp only [CollatzResearch.WordTrace]
  refine ⟨33821555432539716337202239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45095407243386288449602985 33821555432539716337202239)
  ·
    refine ⟨50732333148809574505803359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33821555432539716337202239 50732333148809574505803359)
    ·
      refine ⟨76098499723214361758705039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50732333148809574505803359 76098499723214361758705039)
      ·
        refine ⟨114147749584821542638057559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76098499723214361758705039 114147749584821542638057559)
        ·
          refine ⟨171221624377232313957086339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114147749584821542638057559 171221624377232313957086339)
          ·
            refine ⟨256832436565848470935629509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171221624377232313957086339 256832436565848470935629509)
            ·
              refine ⟨48156081856096588300430533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256832436565848470935629509 48156081856096588300430533)
              ·
                refine ⟨9029265348018110306330725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48156081856096588300430533 9029265348018110306330725)
                ·
                  refine ⟨1692987252753395682437011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9029265348018110306330725 1692987252753395682437011)
                  ·
                    refine ⟨2539480879130093523655517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1692987252753395682437011 2539480879130093523655517)
                    ·
                      refine ⟨952305329673785071370819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539480879130093523655517 952305329673785071370819)
                      ·
                        rfl

theorem cell23_1854608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 1, 3].length) (baseStart_1854608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854608 prefixEnd_1854608 := by exact prefixLift 1854608
  have htrace : WordTrace (prefixWord ++ tailWord_1854608) baseStart_1854608 baseEnd_1854608 := by
    simpa [prefixWord, tailWord_1854608, baseEnd_1854608] using wordTrace_append hprefix tailTrace_1854608
  have hstable : (prefixWord ++ tailWord_1854608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854608).length < 2 ^ (prefixWord ++ tailWord_1854608).sum := by decide
  have hdescent : baseEnd_1854608 < baseStart_1854608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854626 : List Nat := [3, 3, 1, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1854626 : Nat := 118140960795 + 1854626 * 2 ^ 59
def prefixEnd_1854626 : Nat := 4983230072969 + 3 ^ 40 * 1854626 * 2
def baseEnd_1854626 : Nat := 952314572325566000945737

theorem tailTrace_1854626 : CollatzResearch.WordTrace tailWord_1854626 prefixEnd_1854626 952314572325566000945737 := by
  unfold tailWord_1854626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910941844753555437139933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45095844919342814499039821 16910941844753555437139933)
  ·
    refine ⟨6341603191782583288927475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16910941844753555437139933 6341603191782583288927475)
    ·
      refine ⟨9512404787673874933391213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6341603191782583288927475 9512404787673874933391213)
      ·
        refine ⟨3567151795377703100021705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9512404787673874933391213 3567151795377703100021705)
        ·
          refine ⟨2675363846533277325016279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567151795377703100021705 2675363846533277325016279)
          ·
            refine ⟨4013045769799915987524419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675363846533277325016279 4013045769799915987524419)
            ·
              refine ⟨6019568654699873981286629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013045769799915987524419 6019568654699873981286629)
              ·
                refine ⟨1128669122756226371491243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6019568654699873981286629 1128669122756226371491243)
                ·
                  refine ⟨1693003684134339557236865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128669122756226371491243 1693003684134339557236865)
                  ·
                    refine ⟨1269752763100754667927649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1693003684134339557236865 1269752763100754667927649)
                    ·
                      refine ⟨952314572325566000945737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269752763100754667927649 952314572325566000945737)
                      ·
                        rfl

theorem cell23_1854626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1854626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854626 prefixEnd_1854626 := by exact prefixLift 1854626
  have htrace : WordTrace (prefixWord ++ tailWord_1854626) baseStart_1854626 baseEnd_1854626 := by
    simpa [prefixWord, tailWord_1854626, baseEnd_1854626] using wordTrace_append hprefix tailTrace_1854626
  have hstable : (prefixWord ++ tailWord_1854626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854626).length < 2 ^ (prefixWord ++ tailWord_1854626).sum := by decide
  have hdescent : baseEnd_1854626 < baseStart_1854626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854651 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5]
def baseStart_1854651 : Nat := 118140960795 + 1854651 * 2 ^ 59
def prefixEnd_1854651 : Nat := 4983230072969 + 3 ^ 40 * 1854651 * 2
def baseEnd_1854651 : Nat := 952327409341928403133121

theorem tailTrace_1854651 : CollatzResearch.WordTrace tailWord_1854651 prefixEnd_1854651 952327409341928403133121 := by
  unfold tailWord_1854651
  simp only [CollatzResearch.WordTrace]
  refine ⟨67644679203923651018219807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45096452802615767345479871 67644679203923651018219807)
  ·
    refine ⟨101467018805885476527329711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67644679203923651018219807 101467018805885476527329711)
    ·
      refine ⟨152200528208828214790994567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101467018805885476527329711 152200528208828214790994567)
      ·
        refine ⟨228300792313242322186491851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152200528208828214790994567 228300792313242322186491851)
        ·
          refine ⟨342451188469863483279737777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228300792313242322186491851 342451188469863483279737777)
          ·
            refine ⟨256838391352397612459803333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342451188469863483279737777 256838391352397612459803333)
            ·
              refine ⟨48157198378574552336213125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 256838391352397612459803333 48157198378574552336213125)
              ·
                refine ⟨9029474695982728563039961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48157198378574552336213125 9029474695982728563039961)
                ·
                  refine ⟨6772106021987046422279971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9029474695982728563039961 6772106021987046422279971)
                  ·
                    refine ⟨10158159032980569633419957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6772106021987046422279971 10158159032980569633419957)
                    ·
                      refine ⟨952327409341928403133121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10158159032980569633419957 952327409341928403133121)
                      ·
                        rfl

theorem cell23_1854651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_1854651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854651 prefixEnd_1854651 := by exact prefixLift 1854651
  have htrace : WordTrace (prefixWord ++ tailWord_1854651) baseStart_1854651 baseEnd_1854651 := by
    simpa [prefixWord, tailWord_1854651, baseEnd_1854651] using wordTrace_append hprefix tailTrace_1854651
  have hstable : (prefixWord ++ tailWord_1854651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854651).length < 2 ^ (prefixWord ++ tailWord_1854651).sum := by decide
  have hdescent : baseEnd_1854651 < baseStart_1854651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854661 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_1854661 : Nat := 118140960795 + 1854661 * 2 ^ 59
def prefixEnd_1854661 : Nat := 4983230072969 + 3 ^ 40 * 1854661 * 2
def baseEnd_1854661 : Nat := 952332544148473364008075

theorem tailTrace_1854661 : CollatzResearch.WordTrace tailWord_1854661 prefixEnd_1854661 952332544148473364008075 := by
  unfold tailWord_1854661
  simp only [CollatzResearch.WordTrace]
  refine ⟨67645043933887422726083837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45096695955924948484055891 67645043933887422726083837)
  ·
    refine ⟨25366891475207783522281439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67645043933887422726083837 25366891475207783522281439)
    ·
      refine ⟨38050337212811675283422159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25366891475207783522281439 38050337212811675283422159)
      ·
        refine ⟨57075505819217512925133239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38050337212811675283422159 57075505819217512925133239)
        ·
          refine ⟨85613258728826269387699859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57075505819217512925133239 85613258728826269387699859)
          ·
            refine ⟨128419888093239404081549789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85613258728826269387699859 128419888093239404081549789)
            ·
              refine ⟨48157458034964776530581171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128419888093239404081549789 48157458034964776530581171)
              ·
                refine ⟨72236187052447164795871757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48157458034964776530581171 72236187052447164795871757)
                ·
                  refine ⟨27088570144667686798451909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72236187052447164795871757 27088570144667686798451909)
                  ·
                    refine ⟨5079106902125191274709733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27088570144667686798451909 5079106902125191274709733)
                    ·
                      refine ⟨952332544148473364008075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5079106902125191274709733 952332544148473364008075)
                      ·
                        rfl

theorem cell23_1854661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_1854661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854661 prefixEnd_1854661 := by exact prefixLift 1854661
  have htrace : WordTrace (prefixWord ++ tailWord_1854661) baseStart_1854661 baseEnd_1854661 := by
    simpa [prefixWord, tailWord_1854661, baseEnd_1854661] using wordTrace_append hprefix tailTrace_1854661
  have hstable : (prefixWord ++ tailWord_1854661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854661).length < 2 ^ (prefixWord ++ tailWord_1854661).sum := by decide
  have hdescent : baseEnd_1854661 < baseStart_1854661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854676 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1854676 : Nat := 118140960795 + 1854676 * 2 ^ 59
def prefixEnd_1854676 : Nat := 4983230072969 + 3 ^ 40 * 1854676 * 2
def baseEnd_1854676 : Nat := 952340246358290805320507

theorem tailTrace_1854676 : CollatzResearch.WordTrace tailWord_1854676 prefixEnd_1854676 952340246358290805320507 := by
  unfold tailWord_1854676
  simp only [CollatzResearch.WordTrace]
  refine ⟨33822795514416540143939941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45097060685888720191919921 33822795514416540143939941)
  ·
    refine ⟨6341774158953101276988739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33822795514416540143939941 6341774158953101276988739)
    ·
      refine ⟨9512661238429651915483109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6341774158953101276988739 9512661238429651915483109)
      ·
        refine ⟨1783623982205559734153083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9512661238429651915483109 1783623982205559734153083)
        ·
          refine ⟨2675435973308339601229625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783623982205559734153083 2675435973308339601229625)
          ·
            refine ⟨2006576979981254700922219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675435973308339601229625 2006576979981254700922219)
            ·
              refine ⟨3009865469971882051383329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006576979981254700922219 3009865469971882051383329)
              ·
                refine ⟨2257399102478911538537497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3009865469971882051383329 2257399102478911538537497)
                ·
                  refine ⟨1693049326859183653903123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257399102478911538537497 1693049326859183653903123)
                  ·
                    refine ⟨2539573990288775480854685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1693049326859183653903123 2539573990288775480854685)
                    ·
                      refine ⟨952340246358290805320507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539573990288775480854685 952340246358290805320507)
                      ·
                        rfl

theorem cell23_1854676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1854676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854676 prefixEnd_1854676 := by exact prefixLift 1854676
  have htrace : WordTrace (prefixWord ++ tailWord_1854676) baseStart_1854676 baseEnd_1854676 := by
    simpa [prefixWord, tailWord_1854676, baseEnd_1854676] using wordTrace_append hprefix tailTrace_1854676
  have hstable : (prefixWord ++ tailWord_1854676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854676).length < 2 ^ (prefixWord ++ tailWord_1854676).sum := by decide
  have hdescent : baseEnd_1854676 < baseStart_1854676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854688 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 7]
def baseStart_1854688 : Nat := 118140960795 + 1854688 * 2 ^ 59
def prefixEnd_1854688 : Nat := 4983230072969 + 3 ^ 40 * 1854688 * 2
def baseEnd_1854688 : Nat := 105816267569571639818939

theorem tailTrace_1854688 : CollatzResearch.WordTrace tailWord_1854688 prefixEnd_1854688 105816267569571639818939 := by
  unfold tailWord_1854688
  simp only [CollatzResearch.WordTrace]
  refine ⟨33823014352394803168658359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45097352469859737558211145 33823014352394803168658359)
  ·
    refine ⟨50734521528592204752987539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33823014352394803168658359 50734521528592204752987539)
    ·
      refine ⟨76101782292888307129481309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50734521528592204752987539 76101782292888307129481309)
      ·
        refine ⟨28538168359833115173555491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76101782292888307129481309 28538168359833115173555491)
        ·
          refine ⟨42807252539749672760333237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28538168359833115173555491 42807252539749672760333237)
          ·
            refine ⟨4013179925601531821281241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42807252539749672760333237 4013179925601531821281241)
            ·
              refine ⟨3009884944201148865960931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4013179925601531821281241 3009884944201148865960931)
              ·
                refine ⟨4514827416301723298941397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3009884944201148865960931 4514827416301723298941397)
                ·
                  refine ⟨105816267569571639818939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4514827416301723298941397 105816267569571639818939)
                  ·
                    rfl

theorem cell23_1854688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 7].length) (baseStart_1854688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854688 prefixEnd_1854688 := by exact prefixLift 1854688
  have htrace : WordTrace (prefixWord ++ tailWord_1854688) baseStart_1854688 baseEnd_1854688 := by
    simpa [prefixWord, tailWord_1854688, baseEnd_1854688] using wordTrace_append hprefix tailTrace_1854688
  have hstable : (prefixWord ++ tailWord_1854688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854688).length < 2 ^ (prefixWord ++ tailWord_1854688).sum := by decide
  have hdescent : baseEnd_1854688 < baseStart_1854688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854699 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 2, 2, 2]
def baseStart_1854699 : Nat := 118140960795 + 1854699 * 2 ^ 59
def prefixEnd_1854699 : Nat := 4983230072969 + 3 ^ 40 * 1854699 * 2
def baseEnd_1854699 : Nat := 952352056413344215332901

theorem tailTrace_1854699 : CollatzResearch.WordTrace tailWord_1854699 prefixEnd_1854699 952352056413344215332901 := by
  unfold tailWord_1854699
  simp only [CollatzResearch.WordTrace]
  refine ⟨67646429907749755215967151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45097619938499836810644767 67646429907749755215967151)
  ·
    refine ⟨101469644861624632823950727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67646429907749755215967151 101469644861624632823950727)
    ·
      refine ⟨152204467292436949235926091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101469644861624632823950727 152204467292436949235926091)
      ·
        refine ⟨228306700938655423853889137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152204467292436949235926091 228306700938655423853889137)
        ·
          refine ⟨171230025703991567890416853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228306700938655423853889137 171230025703991567890416853)
          ·
            refine ⟨4013203727437302372431645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 171230025703991567890416853 4013203727437302372431645)
            ·
              refine ⟨1504951397788988389661867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4013203727437302372431645 1504951397788988389661867)
              ·
                refine ⟨2257427096683482584492801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504951397788988389661867 2257427096683482584492801)
                ·
                  refine ⟨1693070322512611938369601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257427096683482584492801 1693070322512611938369601)
                  ·
                    refine ⟨1269802741884458953777201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1693070322512611938369601 1269802741884458953777201)
                    ·
                      refine ⟨952352056413344215332901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269802741884458953777201 952352056413344215332901)
                      ·
                        rfl

theorem cell23_1854699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 2, 2].length) (baseStart_1854699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854699 prefixEnd_1854699 := by exact prefixLift 1854699
  have htrace : WordTrace (prefixWord ++ tailWord_1854699) baseStart_1854699 baseEnd_1854699 := by
    simpa [prefixWord, tailWord_1854699, baseEnd_1854699] using wordTrace_append hprefix tailTrace_1854699
  have hstable : (prefixWord ++ tailWord_1854699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854699).length < 2 ^ (prefixWord ++ tailWord_1854699).sum := by decide
  have hdescent : baseEnd_1854699 < baseStart_1854699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854711 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1854711 : Nat := 118140960795 + 1854711 * 2 ^ 59
def prefixEnd_1854711 : Nat := 4983230072969 + 3 ^ 40 * 1854711 * 2
def baseEnd_1854711 : Nat := 952358218181198168382845

theorem tailTrace_1854711 : CollatzResearch.WordTrace tailWord_1854711 prefixEnd_1854711 952358218181198168382845 := by
  unfold tailWord_1854711
  simp only [CollatzResearch.WordTrace]
  refine ⟨67646867583706281265403987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45097911722470854176935991 67646867583706281265403987)
  ·
    refine ⟨101470301375559421898105981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67646867583706281265403987 101470301375559421898105981)
    ·
      refine ⟨38051363015834783211789743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101470301375559421898105981 38051363015834783211789743)
      ·
        refine ⟨57077044523752174817684615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38051363015834783211789743 57077044523752174817684615)
        ·
          refine ⟨85615566785628262226526923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57077044523752174817684615 85615566785628262226526923)
          ·
            refine ⟨128423350178442393339790385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85615566785628262226526923 128423350178442393339790385)
            ·
              refine ⟨96317512633831795004842789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128423350178442393339790385 96317512633831795004842789)
              ·
                refine ⟨18059533618843461563408023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96317512633831795004842789 18059533618843461563408023)
                ·
                  refine ⟨27089300428265192345112035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18059533618843461563408023 27089300428265192345112035)
                  ·
                    refine ⟨40633950642397788517668053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27089300428265192345112035 40633950642397788517668053)
                    ·
                      refine ⟨952358218181198168382845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40633950642397788517668053 952358218181198168382845)
                      ·
                        rfl

theorem cell23_1854711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1854711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854711 prefixEnd_1854711 := by exact prefixLift 1854711
  have htrace : WordTrace (prefixWord ++ tailWord_1854711) baseStart_1854711 baseEnd_1854711 := by
    simpa [prefixWord, tailWord_1854711, baseEnd_1854711] using wordTrace_append hprefix tailTrace_1854711
  have hstable : (prefixWord ++ tailWord_1854711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854711).length < 2 ^ (prefixWord ++ tailWord_1854711).sum := by decide
  have hdescent : baseEnd_1854711 < baseStart_1854711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854750 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1854750 : Nat := 118140960795 + 1854750 * 2 ^ 59
def prefixEnd_1854750 : Nat := 4983230072969 + 3 ^ 40 * 1854750 * 2
def baseEnd_1854750 : Nat := 952378243926723515795167

theorem tailTrace_1854750 : CollatzResearch.WordTrace tailWord_1854750 prefixEnd_1854750 952378243926723515795167 := by
  unfold tailWord_1854750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456036253820623865759213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45098860020376660617382469 8456036253820623865759213)
  ·
    refine ⟨3171013595182733949659705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8456036253820623865759213 3171013595182733949659705)
    ·
      refine ⟨2378260196387050462244779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3171013595182733949659705 2378260196387050462244779)
      ·
        refine ⟨3567390294580575693367169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378260196387050462244779 3567390294580575693367169)
        ·
          refine ⟨2675542720935431770025377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567390294580575693367169 2675542720935431770025377)
          ·
            refine ⟨2006657040701573827519033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675542720935431770025377 2006657040701573827519033)
            ·
              refine ⟨1504992780526180370639275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006657040701573827519033 1504992780526180370639275)
              ·
                refine ⟨2257489170789270555958913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504992780526180370639275 2257489170789270555958913)
                ·
                  refine ⟨1693116878091952916969185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257489170789270555958913 1693116878091952916969185)
                  ·
                    refine ⟨1269837658568964687726889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1693116878091952916969185 1269837658568964687726889)
                    ·
                      refine ⟨952378243926723515795167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269837658568964687726889 952378243926723515795167)
                      ·
                        rfl

theorem cell23_1854750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1854750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854750 prefixEnd_1854750 := by exact prefixLift 1854750
  have htrace : WordTrace (prefixWord ++ tailWord_1854750) baseStart_1854750 baseEnd_1854750 := by
    simpa [prefixWord, tailWord_1854750, baseEnd_1854750] using wordTrace_append hprefix tailTrace_1854750
  have hstable : (prefixWord ++ tailWord_1854750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854750).length < 2 ^ (prefixWord ++ tailWord_1854750).sum := by decide
  have hdescent : baseEnd_1854750 < baseStart_1854750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854772 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1854772 : Nat := 118140960795 + 1854772 * 2 ^ 59
def prefixEnd_1854772 : Nat := 4983230072969 + 3 ^ 40 * 1854772 * 2
def baseEnd_1854772 : Nat := 952389540501122429720065

theorem tailTrace_1854772 : CollatzResearch.WordTrace tailWord_1854772 prefixEnd_1854772 952389540501122429720065 := by
  unfold tailWord_1854772
  simp only [CollatzResearch.WordTrace]
  refine ⟨33824546218242644341687285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45099394957656859122249713 33824546218242644341687285)
  ·
    refine ⟨3171051207960247907033183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33824546218242644341687285 3171051207960247907033183)
    ·
      refine ⟨4756576811940371860549775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3171051207960247907033183 4756576811940371860549775)
      ·
        refine ⟨7134865217910557790824663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4756576811940371860549775 7134865217910557790824663)
        ·
          refine ⟨10702297826865836686236995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7134865217910557790824663 10702297826865836686236995)
          ·
            refine ⟨16053446740298755029355493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10702297826865836686236995 16053446740298755029355493)
            ·
              refine ⟨3010021263806016568004155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16053446740298755029355493 3010021263806016568004155)
              ·
                refine ⟨4515031895709024852006233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010021263806016568004155 4515031895709024852006233)
                ·
                  refine ⟨3386273921781768639004675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515031895709024852006233 3386273921781768639004675)
                  ·
                    refine ⟨5079410882672652958507013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3386273921781768639004675 5079410882672652958507013)
                    ·
                      refine ⟨952389540501122429720065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5079410882672652958507013 952389540501122429720065)
                      ·
                        rfl

theorem cell23_1854772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1854772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854772 prefixEnd_1854772 := by exact prefixLift 1854772
  have htrace : WordTrace (prefixWord ++ tailWord_1854772) baseStart_1854772 baseEnd_1854772 := by
    simpa [prefixWord, tailWord_1854772, baseEnd_1854772] using wordTrace_append hprefix tailTrace_1854772
  have hstable : (prefixWord ++ tailWord_1854772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854772).length < 2 ^ (prefixWord ++ tailWord_1854772).sum := by decide
  have hdescent : baseEnd_1854772 < baseStart_1854772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854790 : List Nat := [6, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1854790 : Nat := 118140960795 + 1854790 * 2 ^ 59
def prefixEnd_1854790 : Nat := 4983230072969 + 3 ^ 40 * 1854790 * 2
def baseEnd_1854790 : Nat := 105822087016989262143887

theorem tailTrace_1854790 : CollatzResearch.WordTrace tailWord_1854790 prefixEnd_1854790 105822087016989262143887 := by
  unfold tailWord_1854790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114054654700627429922807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45099832633613385171686549 2114054654700627429922807)
  ·
    refine ⟨3171081982050941144884211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2114054654700627429922807 3171081982050941144884211)
    ·
      refine ⟨4756622973076411717326317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3171081982050941144884211 4756622973076411717326317)
      ·
        refine ⟨1783733614903654393997369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4756622973076411717326317 1783733614903654393997369)
        ·
          refine ⟨1337800211177740795498027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1783733614903654393997369 1337800211177740795498027)
          ·
            refine ⟨2006700316766611193247041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337800211177740795498027 2006700316766611193247041)
            ·
              refine ⟨1505025237574958394935281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006700316766611193247041 1505025237574958394935281)
              ·
                refine ⟨1128768928181218796201461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505025237574958394935281 1128768928181218796201461)
                ·
                  refine ⟨105822087016989262143887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1128768928181218796201461 105822087016989262143887)
                  ·
                    rfl

theorem cell23_1854790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1854790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854790 prefixEnd_1854790 := by exact prefixLift 1854790
  have htrace : WordTrace (prefixWord ++ tailWord_1854790) baseStart_1854790 baseEnd_1854790 := by
    simpa [prefixWord, tailWord_1854790, baseEnd_1854790] using wordTrace_append hprefix tailTrace_1854790
  have hstable : (prefixWord ++ tailWord_1854790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854790).length < 2 ^ (prefixWord ++ tailWord_1854790).sum := by decide
  have hdescent : baseEnd_1854790 < baseStart_1854790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854798 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1854798 : Nat := 118140960795 + 1854798 * 2 ^ 59
def prefixEnd_1854798 : Nat := 4983230072969 + 3 ^ 40 * 1854798 * 2
def baseEnd_1854798 : Nat := 952402890998139327994945

theorem tailTrace_1854798 : CollatzResearch.WordTrace tailWord_1854798 prefixEnd_1854798 952402890998139327994945 := by
  unfold tailWord_1854798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456255091798886890477631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45100027156260730082547365 8456255091798886890477631)
  ·
    refine ⟨12684382637698330335716447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8456255091798886890477631 12684382637698330335716447)
    ·
      refine ⟨19026573956547495503574671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12684382637698330335716447 19026573956547495503574671)
      ·
        refine ⟨28539860934821243255362007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19026573956547495503574671 28539860934821243255362007)
        ·
          refine ⟨42809791402231864883043011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28539860934821243255362007 42809791402231864883043011)
          ·
            refine ⟨64214687103347797324564517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42809791402231864883043011 64214687103347797324564517)
            ·
              refine ⟨12040253831877711998355847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64214687103347797324564517 12040253831877711998355847)
              ·
                refine ⟨18060380747816567997533771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12040253831877711998355847 18060380747816567997533771)
                ·
                  refine ⟨27090571121724851996300657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18060380747816567997533771 27090571121724851996300657)
                  ·
                    refine ⟨20317928341293638997225493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27090571121724851996300657 20317928341293638997225493)
                    ·
                      refine ⟨952402890998139327994945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20317928341293638997225493 952402890998139327994945)
                      ·
                        rfl

theorem cell23_1854798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1854798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854798 prefixEnd_1854798 := by exact prefixLift 1854798
  have htrace : WordTrace (prefixWord ++ tailWord_1854798) baseStart_1854798 baseEnd_1854798 := by
    simpa [prefixWord, tailWord_1854798, baseEnd_1854798] using wordTrace_append hprefix tailTrace_1854798
  have hstable : (prefixWord ++ tailWord_1854798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854798).length < 2 ^ (prefixWord ++ tailWord_1854798).sum := by decide
  have hdescent : baseEnd_1854798 < baseStart_1854798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854808 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 5, 5]
def baseStart_1854808 : Nat := 118140960795 + 1854808 * 2 ^ 59
def prefixEnd_1854808 : Nat := 4983230072969 + 3 ^ 40 * 1854808 * 2
def baseEnd_1854808 : Nat := 317469341934894762956633

theorem tailTrace_1854808 : CollatzResearch.WordTrace tailWord_1854808 prefixEnd_1854808 317469341934894762956633 := by
  unfold tailWord_1854808
  simp only [CollatzResearch.WordTrace]
  refine ⟨33825202732177433415842539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45100270309569911221123385 33825202732177433415842539)
  ·
    refine ⟨50737804098266150123763809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33825202732177433415842539 50737804098266150123763809)
    ·
      refine ⟨38053353073699612592822857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50737804098266150123763809 38053353073699612592822857)
      ·
        refine ⟨28540014805274709444617143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38053353073699612592822857 28540014805274709444617143)
        ·
          refine ⟨42810022207912064166925715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28540014805274709444617143 42810022207912064166925715)
          ·
            refine ⟨64215033311868096250388573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42810022207912064166925715 64215033311868096250388573)
            ·
              refine ⟨24080637491950536093895715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64215033311868096250388573 24080637491950536093895715)
              ·
                refine ⟨36120956237925804140843573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24080637491950536093895715 36120956237925804140843573)
                ·
                  refine ⟨3386339647305544138204085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36120956237925804140843573 3386339647305544138204085)
                  ·
                    refine ⟨317469341934894762956633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3386339647305544138204085 317469341934894762956633)
                    ·
                      rfl

theorem cell23_1854808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_1854808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854808 prefixEnd_1854808 := by exact prefixLift 1854808
  have htrace : WordTrace (prefixWord ++ tailWord_1854808) baseStart_1854808 baseEnd_1854808 := by
    simpa [prefixWord, tailWord_1854808, baseEnd_1854808] using wordTrace_append hprefix tailTrace_1854808
  have hstable : (prefixWord ++ tailWord_1854808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854808).length < 2 ^ (prefixWord ++ tailWord_1854808).sum := by decide
  have hdescent : baseEnd_1854808 < baseStart_1854808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854815 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 1, 5, 2]
def baseStart_1854815 : Nat := 118140960795 + 1854815 * 2 ^ 59
def prefixEnd_1854815 : Nat := 4983230072969 + 3 ^ 40 * 1854815 * 2
def baseEnd_1854815 : Nat := 952411620169265761482367

theorem tailTrace_1854815 : CollatzResearch.WordTrace tailWord_1854815 prefixEnd_1854815 952411620169265761482367 := by
  unfold tailWord_1854815
  simp only [CollatzResearch.WordTrace]
  refine ⟨67650660775329507027189899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45100440516886338018126599 67650660775329507027189899)
  ·
    refine ⟨101475991162994260540784849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67650660775329507027189899 101475991162994260540784849)
    ·
      refine ⟨76106993372245695405588637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101475991162994260540784849 76106993372245695405588637)
      ·
        refine ⟨28540122514592135777095739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76106993372245695405588637 28540122514592135777095739)
        ·
          refine ⟨42810183771888203665643609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28540122514592135777095739 42810183771888203665643609)
          ·
            refine ⟨32107637828916152749232707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42810183771888203665643609 32107637828916152749232707)
            ·
              refine ⟨48161456743374229123849061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32107637828916152749232707 48161456743374229123849061)
              ·
                refine ⟨9030273139382667960721699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48161456743374229123849061 9030273139382667960721699)
                ·
                  refine ⟨13545409709074001941082549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9030273139382667960721699 13545409709074001941082549)
                  ·
                    refine ⟨1269882160225687681976489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13545409709074001941082549 1269882160225687681976489)
                    ·
                      refine ⟨952411620169265761482367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269882160225687681976489 952411620169265761482367)
                      ·
                        rfl

theorem cell23_1854815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_1854815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854815 prefixEnd_1854815 := by exact prefixLift 1854815
  have htrace : WordTrace (prefixWord ++ tailWord_1854815) baseStart_1854815 baseEnd_1854815 := by
    simpa [prefixWord, tailWord_1854815, baseEnd_1854815] using wordTrace_append hprefix tailTrace_1854815
  have hstable : (prefixWord ++ tailWord_1854815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854815).length < 2 ^ (prefixWord ++ tailWord_1854815).sum := by decide
  have hdescent : baseEnd_1854815 < baseStart_1854815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854826 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1854826 : Nat := 118140960795 + 1854826 * 2 ^ 59
def prefixEnd_1854826 : Nat := 4983230072969 + 3 ^ 40 * 1854826 * 2
def baseEnd_1854826 : Nat := 952417268456465218444817

theorem tailTrace_1854826 : CollatzResearch.WordTrace tailWord_1854826 prefixEnd_1854826 952417268456465218444817 := by
  unfold tailWord_1854826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16912765494572413976460083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45100707985526437270560221 16912765494572413976460083)
  ·
    refine ⟨25369148241858620964690125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16912765494572413976460083 25369148241858620964690125)
    ·
      refine ⟨9513430590696982861758797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25369148241858620964690125 9513430590696982861758797)
      ·
        refine ⟨3567536471511368573159549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9513430590696982861758797 3567536471511368573159549)
        ·
          refine ⟨1337826176816763214934831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3567536471511368573159549 1337826176816763214934831)
          ·
            refine ⟨2006739265225144822402247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337826176816763214934831 2006739265225144822402247)
            ·
              refine ⟨3010108897837717233603371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006739265225144822402247 3010108897837717233603371)
              ·
                refine ⟨4515163346756575850405057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010108897837717233603371 4515163346756575850405057)
                ·
                  refine ⟨3386372510067431887803793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515163346756575850405057 3386372510067431887803793)
                  ·
                    refine ⟨2539779382550573915852845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3386372510067431887803793 2539779382550573915852845)
                    ·
                      refine ⟨952417268456465218444817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539779382550573915852845 952417268456465218444817)
                      ·
                        rfl

theorem cell23_1854826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1854826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854826 prefixEnd_1854826 := by exact prefixLift 1854826
  have htrace : WordTrace (prefixWord ++ tailWord_1854826) baseStart_1854826 baseEnd_1854826 := by
    simpa [prefixWord, tailWord_1854826, baseEnd_1854826] using wordTrace_append hprefix tailTrace_1854826
  have hstable : (prefixWord ++ tailWord_1854826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854826).length < 2 ^ (prefixWord ++ tailWord_1854826).sum := by decide
  have hdescent : baseEnd_1854826 < baseStart_1854826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854839 : List Nat := [1, 1, 3, 1, 1, 2, 6, 3, 1, 1, 3]
def baseStart_1854839 : Nat := 118140960795 + 1854839 * 2 ^ 59
def prefixEnd_1854839 : Nat := 4983230072969 + 3 ^ 40 * 1854839 * 2
def baseEnd_1854839 : Nat := 952423943704973667582257

theorem tailTrace_1854839 : CollatzResearch.WordTrace tailWord_1854839 prefixEnd_1854839 952423943704973667582257 := by
  unfold tailWord_1854839
  simp only [CollatzResearch.WordTrace]
  refine ⟨67651536127242559126063571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45101024084828372750709047 67651536127242559126063571)
  ·
    refine ⟨101477304190863838689095357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67651536127242559126063571 101477304190863838689095357)
    ·
      refine ⟨38053989071573939508410759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101477304190863838689095357 38053989071573939508410759)
      ·
        refine ⟨57080983607360909262616139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38053989071573939508410759 57080983607360909262616139)
        ·
          refine ⟨85621475411041363893924209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57080983607360909262616139 85621475411041363893924209)
          ·
            refine ⟨64216106558281022920443157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85621475411041363893924209 64216106558281022920443157)
            ·
              refine ⟨3010129994919422949395773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64216106558281022920443157 3010129994919422949395773)
              ·
                refine ⟨1128798748094783606023415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3010129994919422949395773 1128798748094783606023415)
                ·
                  refine ⟨1693198122142175409035123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128798748094783606023415 1693198122142175409035123)
                  ·
                    refine ⟨2539797183213263113552685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1693198122142175409035123 2539797183213263113552685)
                    ·
                      refine ⟨952423943704973667582257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539797183213263113552685 952423943704973667582257)
                      ·
                        rfl

theorem cell23_1854839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_1854839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854839 prefixEnd_1854839 := by exact prefixLift 1854839
  have htrace : WordTrace (prefixWord ++ tailWord_1854839) baseStart_1854839 baseEnd_1854839 := by
    simpa [prefixWord, tailWord_1854839, baseEnd_1854839] using wordTrace_append hprefix tailTrace_1854839
  have hstable : (prefixWord ++ tailWord_1854839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854839).length < 2 ^ (prefixWord ++ tailWord_1854839).sum := by decide
  have hdescent : baseEnd_1854839 < baseStart_1854839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854846 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_1854846 : Nat := 118140960795 + 1854846 * 2 ^ 59
def prefixEnd_1854846 : Nat := 4983230072969 + 3 ^ 40 * 1854846 * 2
def baseEnd_1854846 : Nat := 105825282007728348910525

theorem tailTrace_1854846 : CollatzResearch.WordTrace tailWord_1854846 prefixEnd_1854846 105825282007728348910525 := by
  unfold tailWord_1854846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456473929777149915196049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45101194292144799547712261 8456473929777149915196049)
  ·
    refine ⟨6342355447332862436397037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8456473929777149915196049 6342355447332862436397037)
    ·
      refine ⟨2378383292749823413648889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6342355447332862436397037 2378383292749823413648889)
      ·
        refine ⟨1783787469562367560236667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2378383292749823413648889 1783787469562367560236667)
        ·
          refine ⟨2675681204343551340355001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783787469562367560236667 2675681204343551340355001)
          ·
            refine ⟨2006760903257663505266251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675681204343551340355001 2006760903257663505266251)
            ·
              refine ⟨3010141354886495257899377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006760903257663505266251 3010141354886495257899377)
              ·
                refine ⟨2257606016164871443424533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010141354886495257899377 2257606016164871443424533)
                ·
                  refine ⟨105825282007728348910525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2257606016164871443424533 105825282007728348910525)
                  ·
                    rfl

theorem cell23_1854846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_1854846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854846 prefixEnd_1854846 := by exact prefixLift 1854846
  have htrace : WordTrace (prefixWord ++ tailWord_1854846) baseStart_1854846 baseEnd_1854846 := by
    simpa [prefixWord, tailWord_1854846, baseEnd_1854846] using wordTrace_append hprefix tailTrace_1854846
  have hstable : (prefixWord ++ tailWord_1854846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854846).length < 2 ^ (prefixWord ++ tailWord_1854846).sum := by decide
  have hdescent : baseEnd_1854846 < baseStart_1854846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854848 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1854848 : Nat := 118140960795 + 1854848 * 2 ^ 59
def prefixEnd_1854848 : Nat := 4983230072969 + 3 ^ 40 * 1854848 * 2
def baseEnd_1854848 : Nat := 952428565030864132369715

theorem tailTrace_1854848 : CollatzResearch.WordTrace tailWord_1854848 prefixEnd_1854848 952428565030864132369715 := by
  unfold tailWord_1854848
  simp only [CollatzResearch.WordTrace]
  refine ⟨33825932192104976831570599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45101242922806635775427465 33825932192104976831570599)
  ·
    refine ⟨50738898288157465247355899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33825932192104976831570599 50738898288157465247355899)
    ·
      refine ⟨76108347432236197871033849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50738898288157465247355899 76108347432236197871033849)
      ·
        refine ⟨57081260574177148403275387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76108347432236197871033849 57081260574177148403275387)
        ·
          refine ⟨85621890861265722604913081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57081260574177148403275387 85621890861265722604913081)
          ·
            refine ⟨64216418145949291953684811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85621890861265722604913081 64216418145949291953684811)
            ·
              refine ⟨96324627218923937930527217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64216418145949291953684811 96324627218923937930527217)
              ·
                refine ⟨72243470414192953447895413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96324627218923937930527217 72243470414192953447895413)
                ·
                  refine ⟨6772825351330589385740195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72243470414192953447895413 6772825351330589385740195)
                  ·
                    refine ⟨10159238026995884078610293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6772825351330589385740195 10159238026995884078610293)
                    ·
                      refine ⟨952428565030864132369715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10159238026995884078610293 952428565030864132369715)
                      ·
                        rfl

theorem cell23_1854848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1854848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854848 prefixEnd_1854848 := by exact prefixLift 1854848
  have htrace : WordTrace (prefixWord ++ tailWord_1854848) baseStart_1854848 baseEnd_1854848 := by
    simpa [prefixWord, tailWord_1854848, baseEnd_1854848] using wordTrace_append hprefix tailTrace_1854848
  have hstable : (prefixWord ++ tailWord_1854848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854848).length < 2 ^ (prefixWord ++ tailWord_1854848).sum := by decide
  have hdescent : baseEnd_1854848 < baseStart_1854848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854879 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 3, 2, 2]
def baseStart_1854879 : Nat := 118140960795 + 1854879 * 2 ^ 59
def prefixEnd_1854879 : Nat := 4983230072969 + 3 ^ 40 * 1854879 * 2
def baseEnd_1854879 : Nat := 952444482931153511082073

theorem tailTrace_1854879 : CollatzResearch.WordTrace tailWord_1854879 prefixEnd_1854879 952444482931153511082073 := by
  unfold tailWord_1854879
  simp only [CollatzResearch.WordTrace]
  refine ⟨67652995047097645957519691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45101996698065097305013127 67652995047097645957519691)
  ·
    refine ⟨101479492570646468936279537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67652995047097645957519691 101479492570646468936279537)
    ·
      refine ⟨76109619427984851702209653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101479492570646468936279537 76109619427984851702209653)
      ·
        refine ⟨7135276821373579847082155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76109619427984851702209653 7135276821373579847082155)
        ·
          refine ⟨10702915232060369770623233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135276821373579847082155 10702915232060369770623233)
          ·
            refine ⟨8027186424045277327967425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10702915232060369770623233 8027186424045277327967425)
            ·
              refine ⟨6020389818033957995975569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027186424045277327967425 6020389818033957995975569)
              ·
                refine ⟨4515292363525468496981677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6020389818033957995975569 4515292363525468496981677)
                ·
                  refine ⟨1693234636322050686368129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4515292363525468496981677 1693234636322050686368129)
                  ·
                    refine ⟨1269925977241538014776097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1693234636322050686368129 1269925977241538014776097)
                    ·
                      refine ⟨952444482931153511082073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269925977241538014776097 952444482931153511082073)
                      ·
                        rfl

theorem cell23_1854879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_1854879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854879 prefixEnd_1854879 := by exact prefixLift 1854879
  have htrace : WordTrace (prefixWord ++ tailWord_1854879) baseStart_1854879 baseEnd_1854879 := by
    simpa [prefixWord, tailWord_1854879, baseEnd_1854879] using wordTrace_append hprefix tailTrace_1854879
  have hstable : (prefixWord ++ tailWord_1854879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854879).length < 2 ^ (prefixWord ++ tailWord_1854879).sum := by decide
  have hdescent : baseEnd_1854879 < baseStart_1854879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854895 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 3]
def baseStart_1854895 : Nat := 118140960795 + 1854895 * 2 ^ 59
def prefixEnd_1854895 : Nat := 4983230072969 + 3 ^ 40 * 1854895 * 2
def baseEnd_1854895 : Nat := 952452698621625448481999

theorem tailTrace_1854895 : CollatzResearch.WordTrace tailWord_1854895 prefixEnd_1854895 952452698621625448481999 := by
  unfold tailWord_1854895
  simp only [CollatzResearch.WordTrace]
  refine ⟨67653578615039680690102139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45102385743359787126734759 67653578615039680690102139)
  ·
    refine ⟨101480367922559521035153209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67653578615039680690102139 101480367922559521035153209)
    ·
      refine ⟨76110275941919640776364907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101480367922559521035153209 76110275941919640776364907)
      ·
        refine ⟨114165413912879461164547361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76110275941919640776364907 114165413912879461164547361)
        ·
          refine ⟨85624060434659595873410521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114165413912879461164547361 85624060434659595873410521)
          ·
            refine ⟨64218045325994696905057891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85624060434659595873410521 64218045325994696905057891)
            ·
              refine ⟨96327067988992045357586837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64218045325994696905057891 96327067988992045357586837)
              ·
                refine ⟨4515331311984002126136883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96327067988992045357586837 4515331311984002126136883)
                ·
                  refine ⟨6772996967976003189205325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515331311984002126136883 6772996967976003189205325)
                  ·
                    refine ⟨2539873862991001195951997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6772996967976003189205325 2539873862991001195951997)
                    ·
                      refine ⟨952452698621625448481999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539873862991001195951997 952452698621625448481999)
                      ·
                        rfl

theorem cell23_1854895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_1854895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854895 prefixEnd_1854895 := by exact prefixLift 1854895
  have htrace : WordTrace (prefixWord ++ tailWord_1854895) baseStart_1854895 baseEnd_1854895 := by
    simpa [prefixWord, tailWord_1854895, baseEnd_1854895] using wordTrace_append hprefix tailTrace_1854895
  have hstable : (prefixWord ++ tailWord_1854895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854895).length < 2 ^ (prefixWord ++ tailWord_1854895).sum := by decide
  have hdescent : baseEnd_1854895 < baseStart_1854895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854912 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 4, 1, 3]
def baseStart_1854912 : Nat := 118140960795 + 1854912 * 2 ^ 59
def prefixEnd_1854912 : Nat := 4983230072969 + 3 ^ 40 * 1854912 * 2
def baseEnd_1854912 : Nat := 952461427792751881969421

theorem tailTrace_1854912 : CollatzResearch.WordTrace tailWord_1854912 prefixEnd_1854912 952461427792751881969421 := by
  unfold tailWord_1854912
  simp only [CollatzResearch.WordTrace]
  refine ⟨33827099327989046296735495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45102799103985395062313993 33827099327989046296735495)
  ·
    refine ⟨50740648991983569445103243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33827099327989046296735495 50740648991983569445103243)
    ·
      refine ⟨76110973487975354167654865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50740648991983569445103243 76110973487975354167654865)
      ·
        refine ⟨57083230115981515625741149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76110973487975354167654865 57083230115981515625741149)
        ·
          refine ⟨21406211293493068359652931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57083230115981515625741149 21406211293493068359652931)
          ·
            refine ⟨32109316940239602539479397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21406211293493068359652931 32109316940239602539479397)
            ·
              refine ⟨6020496926294925476152387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32109316940239602539479397 6020496926294925476152387)
              ·
                refine ⟨9030745389442388214228581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020496926294925476152387 9030745389442388214228581)
                ·
                  refine ⟨1693264760520447790167859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9030745389442388214228581 1693264760520447790167859)
                  ·
                    refine ⟨2539897140780671685251789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1693264760520447790167859 2539897140780671685251789)
                    ·
                      refine ⟨952461427792751881969421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2539897140780671685251789 952461427792751881969421)
                      ·
                        rfl

theorem cell23_1854912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_1854912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854912 prefixEnd_1854912 := by exact prefixLift 1854912
  have htrace : WordTrace (prefixWord ++ tailWord_1854912) baseStart_1854912 baseEnd_1854912 := by
    simpa [prefixWord, tailWord_1854912, baseEnd_1854912] using wordTrace_append hprefix tailTrace_1854912
  have hstable : (prefixWord ++ tailWord_1854912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854912).length < 2 ^ (prefixWord ++ tailWord_1854912).sum := by decide
  have hdescent : baseEnd_1854912 < baseStart_1854912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854986 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_1854986 : Nat := 118140960795 + 1854986 * 2 ^ 59
def prefixEnd_1854986 : Nat := 4983230072969 + 3 ^ 40 * 1854986 * 2
def baseEnd_1854986 : Nat := 952499425361184592444081

theorem tailTrace_1854986 : CollatzResearch.WordTrace tailWord_1854986 prefixEnd_1854986 952499425361184592444081 := by
  unfold tailWord_1854986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914224414427500807916203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45104598438473335487776541 16914224414427500807916203)
  ·
    refine ⟨25371336621641251211874305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16914224414427500807916203 25371336621641251211874305)
    ·
      refine ⟨19028502466230938408905729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25371336621641251211874305 19028502466230938408905729)
      ·
        refine ⟨14271376849673203806679297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19028502466230938408905729 14271376849673203806679297)
        ·
          refine ⟨10703532637254902855009473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14271376849673203806679297 10703532637254902855009473)
          ·
            refine ⟨8027649477941177141257105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10703532637254902855009473 8027649477941177141257105)
            ·
              refine ⟨6020737108455882855942829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8027649477941177141257105 6020737108455882855942829)
              ·
                refine ⟨2257776415670956070978561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6020737108455882855942829 2257776415670956070978561)
                ·
                  refine ⟨1693332311753217053233921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257776415670956070978561 1693332311753217053233921)
                  ·
                    refine ⟨1269999233814912789925441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1693332311753217053233921 1269999233814912789925441)
                    ·
                      refine ⟨952499425361184592444081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1269999233814912789925441 952499425361184592444081)
                      ·
                        rfl

theorem cell23_1854986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_1854986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1854986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1854986 prefixEnd_1854986 := by exact prefixLift 1854986
  have htrace : WordTrace (prefixWord ++ tailWord_1854986) baseStart_1854986 baseEnd_1854986 := by
    simpa [prefixWord, tailWord_1854986, baseEnd_1854986] using wordTrace_append hprefix tailTrace_1854986
  have hstable : (prefixWord ++ tailWord_1854986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854986).length < 2 ^ (prefixWord ++ tailWord_1854986).sum := by decide
  have hdescent : baseEnd_1854986 < baseStart_1854986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855009 : List Nat := [1, 2, 3, 2, 2, 3, 2, 3, 5]
def baseStart_1855009 : Nat := 118140960795 + 1855009 * 2 ^ 59
def prefixEnd_1855009 : Nat := 4983230072969 + 3 ^ 40 * 1855009 * 2
def baseEnd_1855009 : Nat := 105834581712915333606275

theorem tailTrace_1855009 : CollatzResearch.WordTrace tailWord_1855009 prefixEnd_1855009 105834581712915333606275 := by
  unfold tailWord_1855009
  simp only [CollatzResearch.WordTrace]
  refine ⟨67657736536626678159752081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45105157691084452106501387 67657736536626678159752081)
  ·
    refine ⟨50743302402470008619814061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67657736536626678159752081 50743302402470008619814061)
    ·
      refine ⟨19028738400926253232430273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50743302402470008619814061 19028738400926253232430273)
      ·
        refine ⟨14271553800694689924322705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19028738400926253232430273 14271553800694689924322705)
        ·
          refine ⟨10703665350521017443242029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14271553800694689924322705 10703665350521017443242029)
          ·
            refine ⟨4013874506445381541215761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10703665350521017443242029 4013874506445381541215761)
            ·
              refine ⟨3010405879834036155911821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4013874506445381541215761 3010405879834036155911821)
              ·
                refine ⟨1128902204937763558466933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3010405879834036155911821 1128902204937763558466933)
                ·
                  refine ⟨105834581712915333606275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1128902204937763558466933 105834581712915333606275)
                  ·
                    rfl

theorem cell23_1855009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 5].length) (baseStart_1855009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855009 prefixEnd_1855009 := by exact prefixLift 1855009
  have htrace : WordTrace (prefixWord ++ tailWord_1855009) baseStart_1855009 baseEnd_1855009 := by
    simpa [prefixWord, tailWord_1855009, baseEnd_1855009] using wordTrace_append hprefix tailTrace_1855009
  have hstable : (prefixWord ++ tailWord_1855009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855009).length < 2 ^ (prefixWord ++ tailWord_1855009).sum := by decide
  have hdescent : baseEnd_1855009 < baseStart_1855009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855055 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_1855055 : Nat := 118140960795 + 1855055 * 2 ^ 59
def prefixEnd_1855055 : Nat := 4983230072969 + 3 ^ 40 * 1855055 * 2
def baseEnd_1855055 : Nat := 952534855526344822481263

theorem tailTrace_1855055 : CollatzResearch.WordTrace tailWord_1855055 prefixEnd_1855055 952534855526344822481263 := by
  unfold tailWord_1855055
  simp only [CollatzResearch.WordTrace]
  refine ⟨67659414294460028015926619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45106276196306685343951079 67659414294460028015926619)
  ·
    refine ⟨101489121441690042023889929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67659414294460028015926619 101489121441690042023889929)
    ·
      refine ⟨76116841081267531517917447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101489121441690042023889929 76116841081267531517917447)
      ·
        refine ⟨114175261621901297276876171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76116841081267531517917447 114175261621901297276876171)
        ·
          refine ⟨171262892432851945915314257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114175261621901297276876171 171262892432851945915314257)
          ·
            refine ⟨128447169324638959436485693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171262892432851945915314257 128447169324638959436485693)
            ·
              refine ⟨48167688496739609788682135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128447169324638959436485693 48167688496739609788682135)
              ·
                refine ⟨72251532745109414683023203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48167688496739609788682135 72251532745109414683023203)
                ·
                  refine ⟨108377299117664122024534805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72251532745109414683023203 108377299117664122024534805)
                  ·
                    refine ⟨5080185896140505719900069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108377299117664122024534805 5080185896140505719900069)
                    ·
                      refine ⟨952534855526344822481263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5080185896140505719900069 952534855526344822481263)
                      ·
                        rfl

theorem cell23_1855055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_1855055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855055 prefixEnd_1855055 := by exact prefixLift 1855055
  have htrace : WordTrace (prefixWord ++ tailWord_1855055) baseStart_1855055 baseEnd_1855055 := by
    simpa [prefixWord, tailWord_1855055, baseEnd_1855055] using wordTrace_append hprefix tailTrace_1855055
  have hstable : (prefixWord ++ tailWord_1855055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855055).length < 2 ^ (prefixWord ++ tailWord_1855055).sum := by decide
  have hdescent : baseEnd_1855055 < baseStart_1855055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855082 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 8]
def baseStart_1855082 : Nat := 118140960795 + 1855082 * 2 ^ 59
def prefixEnd_1855082 : Nat := 4983230072969 + 3 ^ 40 * 1855082 * 2
def baseEnd_1855082 : Nat := 105838746611557357427071

theorem tailTrace_1855082 : CollatzResearch.WordTrace tailWord_1855082 prefixEnd_1855082 105838746611557357427071 := by
  unfold tailWord_1855082
  simp only [CollatzResearch.WordTrace]
  refine ⟨16915099766340552906789875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45106932710241474418106333 16915099766340552906789875)
  ·
    refine ⟨25372649649510829360184813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16915099766340552906789875 25372649649510829360184813)
    ·
      refine ⟨9514743618566561010069305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25372649649510829360184813 9514743618566561010069305)
      ·
        refine ⟨7136057713924920757551979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9514743618566561010069305 7136057713924920757551979)
        ·
          refine ⟨10704086570887381136327969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136057713924920757551979 10704086570887381136327969)
          ·
            refine ⟨8028064928165535852245977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10704086570887381136327969 8028064928165535852245977)
            ·
              refine ⟨6021048696124151889184483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8028064928165535852245977 6021048696124151889184483)
              ·
                refine ⟨9031573044186227833776725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021048696124151889184483 9031573044186227833776725)
                ·
                  refine ⟨105838746611557357427071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9031573044186227833776725 105838746611557357427071)
                  ·
                    rfl

theorem cell23_1855082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_1855082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855082 prefixEnd_1855082 := by exact prefixLift 1855082
  have htrace : WordTrace (prefixWord ++ tailWord_1855082) baseStart_1855082 baseEnd_1855082 := by
    simpa [prefixWord, tailWord_1855082, baseEnd_1855082] using wordTrace_append hprefix tailTrace_1855082
  have hstable : (prefixWord ++ tailWord_1855082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855082).length < 2 ^ (prefixWord ++ tailWord_1855082).sum := by decide
  have hdescent : baseEnd_1855082 < baseStart_1855082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855095 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 9]
def baseStart_1855095 : Nat := 118140960795 + 1855095 * 2 ^ 59
def prefixEnd_1855095 : Nat := 4983230072969 + 3 ^ 40 * 1855095 * 2
def baseEnd_1855095 : Nat := 317518464917508221993693

theorem tailTrace_1855095 : CollatzResearch.WordTrace tailWord_1855095 prefixEnd_1855095 317518464917508221993693 := by
  unfold tailWord_1855095
  simp only [CollatzResearch.WordTrace]
  refine ⟨67660873214315114847382739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45107248809543409898255159 67660873214315114847382739)
  ·
    refine ⟨101491309821472672271074109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67660873214315114847382739 101491309821472672271074109)
    ·
      refine ⟨38059241183052252101652791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101491309821472672271074109 38059241183052252101652791)
      ·
        refine ⟨57088861774578378152479187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38059241183052252101652791 57088861774578378152479187)
        ·
          refine ⟨85633292661867567228718781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57088861774578378152479187 85633292661867567228718781)
          ·
            refine ⟨32112484748200337710769543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85633292661867567228718781 32112484748200337710769543)
            ·
              refine ⟨48168727122300506566154315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32112484748200337710769543 48168727122300506566154315)
              ·
                refine ⟨72253090683450759849231473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48168727122300506566154315 72253090683450759849231473)
                ·
                  refine ⟨54189818012588069886923605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72253090683450759849231473 54189818012588069886923605)
                  ·
                    refine ⟨317518464917508221993693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 54189818012588069886923605 317518464917508221993693)
                    ·
                      rfl

theorem cell23_1855095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_1855095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855095 prefixEnd_1855095 := by exact prefixLift 1855095
  have htrace : WordTrace (prefixWord ++ tailWord_1855095) baseStart_1855095 baseEnd_1855095 := by
    simpa [prefixWord, tailWord_1855095, baseEnd_1855095] using wordTrace_append hprefix tailTrace_1855095
  have hstable : (prefixWord ++ tailWord_1855095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855095).length < 2 ^ (prefixWord ++ tailWord_1855095).sum := by decide
  have hdescent : baseEnd_1855095 < baseStart_1855095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855109 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_1855109 : Nat := 118140960795 + 1855109 * 2 ^ 59
def prefixEnd_1855109 : Nat := 4983230072969 + 3 ^ 40 * 1855109 * 2
def baseEnd_1855109 : Nat := 952562583481687611206015

theorem tailTrace_1855109 : CollatzResearch.WordTrace tailWord_1855109 prefixEnd_1855109 952562583481687611206015 := by
  unfold tailWord_1855109
  simp only [CollatzResearch.WordTrace]
  refine ⟨67661383836264395238392381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45107589224176263492261587 67661383836264395238392381)
  ·
    refine ⟨25373018938599148214397143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67661383836264395238392381 25373018938599148214397143)
    ·
      refine ⟨38059528407898722321595715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25373018938599148214397143 38059528407898722321595715)
      ·
        refine ⟨57089292611848083482393573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38059528407898722321595715 57089292611848083482393573)
        ·
          refine ⟨10704242364721515652948795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57089292611848083482393573 10704242364721515652948795)
          ·
            refine ⟨16056363547082273479423193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10704242364721515652948795 16056363547082273479423193)
            ·
              refine ⟨12042272660311705109567395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16056363547082273479423193 12042272660311705109567395)
              ·
                refine ⟨18063408990467557664351093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12042272660311705109567395 18063408990467557664351093)
                ·
                  refine ⟨1693444592856333531032915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18063408990467557664351093 1693444592856333531032915)
                  ·
                    refine ⟨2540166889284500296549373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1693444592856333531032915 2540166889284500296549373)
                    ·
                      refine ⟨952562583481687611206015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2540166889284500296549373 952562583481687611206015)
                      ·
                        rfl

theorem cell23_1855109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_1855109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855109 prefixEnd_1855109 := by exact prefixLift 1855109
  have htrace : WordTrace (prefixWord ++ tailWord_1855109) baseStart_1855109 baseEnd_1855109 := by
    simpa [prefixWord, tailWord_1855109, baseEnd_1855109] using wordTrace_append hprefix tailTrace_1855109
  have hstable : (prefixWord ++ tailWord_1855109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855109).length < 2 ^ (prefixWord ++ tailWord_1855109).sum := by decide
  have hdescent : baseEnd_1855109 < baseStart_1855109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855136 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 2, 3, 2]
def baseStart_1855136 : Nat := 118140960795 + 1855136 * 2 ^ 59
def prefixEnd_1855136 : Nat := 4983230072969 + 3 ^ 40 * 1855136 * 2
def baseEnd_1855136 : Nat := 952576447459359005568391

theorem tailTrace_1855136 : CollatzResearch.WordTrace tailWord_1855136 prefixEnd_1855136 952576447459359005568391 := by
  unfold tailWord_1855136
  simp only [CollatzResearch.WordTrace]
  refine ⟨33831184303583289424812631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45108245738111052566416841 33831184303583289424812631)
  ·
    refine ⟨50746776455374934137218947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33831184303583289424812631 50746776455374934137218947)
    ·
      refine ⟨76120164683062401205828421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50746776455374934137218947 76120164683062401205828421)
      ·
        refine ⟨14272530878074200226092829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76120164683062401205828421 14272530878074200226092829)
        ·
          refine ⟨5352199079277825084784811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14272530878074200226092829 5352199079277825084784811)
          ·
            refine ⟨8028298618916737627177217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352199079277825084784811 8028298618916737627177217)
            ·
              refine ⟨6021223964187553220382913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8028298618916737627177217 6021223964187553220382913)
              ·
                refine ⟨4515917973140664915287185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6021223964187553220382913 4515917973140664915287185)
                ·
                  refine ⟨3386938479855498686465389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4515917973140664915287185 3386938479855498686465389)
                  ·
                    refine ⟨1270101929945812007424521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3386938479855498686465389 1270101929945812007424521)
                    ·
                      refine ⟨952576447459359005568391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270101929945812007424521 952576447459359005568391)
                      ·
                        rfl

theorem cell23_1855136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_1855136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855136 prefixEnd_1855136 := by exact prefixLift 1855136
  have htrace : WordTrace (prefixWord ++ tailWord_1855136) baseStart_1855136 baseEnd_1855136 := by
    simpa [prefixWord, tailWord_1855136, baseEnd_1855136] using wordTrace_append hprefix tailTrace_1855136
  have hstable : (prefixWord ++ tailWord_1855136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855136).length < 2 ^ (prefixWord ++ tailWord_1855136).sum := by decide
  have hdescent : baseEnd_1855136 < baseStart_1855136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855149 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1855149 : Nat := 118140960795 + 1855149 * 2 ^ 59
def prefixEnd_1855149 : Nat := 4983230072969 + 3 ^ 40 * 1855149 * 2
def baseEnd_1855149 : Nat := 952583122707867454705831

theorem tailTrace_1855149 : CollatzResearch.WordTrace tailWord_1855149 prefixEnd_1855149 952583122707867454705831 := by
  unfold tailWord_1855149
  simp only [CollatzResearch.WordTrace]
  refine ⟨67662842756119482069848501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45108561837412988046565667 67662842756119482069848501)
  ·
    refine ⟨6343391508386201444048297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67662842756119482069848501 6343391508386201444048297)
    ·
      refine ⟨4757543631289651083036223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6343391508386201444048297 4757543631289651083036223)
      ·
        refine ⟨7136315446934476624554335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757543631289651083036223 7136315446934476624554335)
        ·
          refine ⟨10704473170401714936831503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136315446934476624554335 10704473170401714936831503)
          ·
            refine ⟨16056709755602572405247255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10704473170401714936831503 16056709755602572405247255)
            ·
              refine ⟨24085064633403858607870883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16056709755602572405247255 24085064633403858607870883)
              ·
                refine ⟨36127596950105787911806325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24085064633403858607870883 36127596950105787911806325)
                ·
                  refine ⟨3386962214072417616731843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36127596950105787911806325 3386962214072417616731843)
                  ·
                    refine ⟨5080443321108626425097765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3386962214072417616731843 5080443321108626425097765)
                    ·
                      refine ⟨952583122707867454705831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5080443321108626425097765 952583122707867454705831)
                      ·
                        rfl

theorem cell23_1855149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1855149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855149 prefixEnd_1855149 := by exact prefixLift 1855149
  have htrace : WordTrace (prefixWord ++ tailWord_1855149) baseStart_1855149 baseEnd_1855149 := by
    simpa [prefixWord, tailWord_1855149, baseEnd_1855149] using wordTrace_append hprefix tailTrace_1855149
  have hstable : (prefixWord ++ tailWord_1855149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855149).length < 2 ^ (prefixWord ++ tailWord_1855149).sum := by decide
  have hdescent : baseEnd_1855149 < baseStart_1855149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855152 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_1855152 : Nat := 118140960795 + 1855152 * 2 ^ 59
def prefixEnd_1855152 : Nat := 4983230072969 + 3 ^ 40 * 1855152 * 2
def baseEnd_1855152 : Nat := 952584663149830942968317

theorem tailTrace_1855152 : CollatzResearch.WordTrace tailWord_1855152 prefixEnd_1855152 952584663149830942968317 := by
  unfold tailWord_1855152
  simp only [CollatzResearch.WordTrace]
  refine ⟨33831476087554306791103855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45108634783405742388138473 33831476087554306791103855)
  ·
    refine ⟨50747214131331460186655783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33831476087554306791103855 50747214131331460186655783)
    ·
      refine ⟨76120821196997190279983675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50747214131331460186655783 76120821196997190279983675)
      ·
        refine ⟨114181231795495785419975513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76120821196997190279983675 114181231795495785419975513)
        ·
          refine ⟨85635923846621839064981635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114181231795495785419975513 85635923846621839064981635)
          ·
            refine ⟨128453885769932758597472453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85635923846621839064981635 128453885769932758597472453)
            ·
              refine ⟨24085103581862392237026085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128453885769932758597472453 24085103581862392237026085)
              ·
                refine ⟨4515956921599198544442391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24085103581862392237026085 4515956921599198544442391)
                ·
                  refine ⟨6773935382398797816663587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515956921599198544442391 6773935382398797816663587)
                  ·
                    refine ⟨10160903073598196724995381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6773935382398797816663587 10160903073598196724995381)
                    ·
                      refine ⟨952584663149830942968317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10160903073598196724995381 952584663149830942968317)
                      ·
                        rfl

theorem cell23_1855152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_1855152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855152 prefixEnd_1855152 := by exact prefixLift 1855152
  have htrace : WordTrace (prefixWord ++ tailWord_1855152) baseStart_1855152 baseEnd_1855152 := by
    simpa [prefixWord, tailWord_1855152, baseEnd_1855152] using wordTrace_append hprefix tailTrace_1855152
  have hstable : (prefixWord ++ tailWord_1855152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855152).length < 2 ^ (prefixWord ++ tailWord_1855152).sum := by decide
  have hdescent : baseEnd_1855152 < baseStart_1855152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855159 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 1, 6]
def baseStart_1855159 : Nat := 118140960795 + 1855159 * 2 ^ 59
def prefixEnd_1855159 : Nat := 4983230072969 + 3 ^ 40 * 1855159 * 2
def baseEnd_1855159 : Nat := 317529419171470805193595

theorem tailTrace_1855159 : CollatzResearch.WordTrace tailWord_1855159 prefixEnd_1855159 317529419171470805193595 := by
  unfold tailWord_1855159
  simp only [CollatzResearch.WordTrace]
  refine ⟨67663207486083253777712531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45108804990722169185141687 67663207486083253777712531)
  ·
    refine ⟨101494811229124880666568797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67663207486083253777712531 101494811229124880666568797)
    ·
      refine ⟨38060554210921830249963299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101494811229124880666568797 38060554210921830249963299)
      ·
        refine ⟨57090831316382745374944949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38060554210921830249963299 57090831316382745374944949)
        ·
          refine ⟨5352265435910882378901089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57090831316382745374944949 5352265435910882378901089)
          ·
            refine ⟨4014199076933161784175817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5352265435910882378901089 4014199076933161784175817)
            ·
              refine ⟨3010649307699871338131863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014199076933161784175817 3010649307699871338131863)
              ·
                refine ⟨4515973961549807007197795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010649307699871338131863 4515973961549807007197795)
                ·
                  refine ⟨6773960942324710510796693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515973961549807007197795 6773960942324710510796693)
                  ·
                    refine ⟨317529419171470805193595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6773960942324710510796693 317529419171470805193595)
                    ·
                      rfl

theorem cell23_1855159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_1855159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855159 prefixEnd_1855159 := by exact prefixLift 1855159
  have htrace : WordTrace (prefixWord ++ tailWord_1855159) baseStart_1855159 baseEnd_1855159 := by
    simpa [prefixWord, tailWord_1855159, baseEnd_1855159] using wordTrace_append hprefix tailTrace_1855159
  have hstable : (prefixWord ++ tailWord_1855159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855159).length < 2 ^ (prefixWord ++ tailWord_1855159).sum := by decide
  have hdescent : baseEnd_1855159 < baseStart_1855159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855180 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_1855180 : Nat := 118140960795 + 1855180 * 2 ^ 59
def prefixEnd_1855180 : Nat := 4983230072969 + 3 ^ 40 * 1855180 * 2
def baseEnd_1855180 : Nat := 317533013536052277806063

theorem tailTrace_1855180 : CollatzResearch.WordTrace tailWord_1855180 prefixEnd_1855180 317533013536052277806063 := by
  unfold tailWord_1855180
  simp only [CollatzResearch.WordTrace]
  refine ⟨33831986709503587182113497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45109315612671449576151329 33831986709503587182113497)
  ·
    refine ⟨25373990032127690386585123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33831986709503587182113497 25373990032127690386585123)
    ·
      refine ⟨38060985048191535579877685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25373990032127690386585123 38060985048191535579877685)
      ·
        refine ⟨3568217348267956460613533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38060985048191535579877685 3568217348267956460613533)
        ·
          refine ⟨1338081505600483672730075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3568217348267956460613533 1338081505600483672730075)
          ·
            refine ⟨2007122258400725509095113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338081505600483672730075 2007122258400725509095113)
            ·
              refine ⟨1505341693800544131821335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007122258400725509095113 1505341693800544131821335)
              ·
                refine ⟨2258012540700816197732003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505341693800544131821335 2258012540700816197732003)
                ·
                  refine ⟨3387018811051224296598005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258012540700816197732003 3387018811051224296598005)
                  ·
                    refine ⟨317533013536052277806063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3387018811051224296598005 317533013536052277806063)
                    ·
                      rfl

theorem cell23_1855180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_1855180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855180 prefixEnd_1855180 := by exact prefixLift 1855180
  have htrace : WordTrace (prefixWord ++ tailWord_1855180) baseStart_1855180 baseEnd_1855180 := by
    simpa [prefixWord, tailWord_1855180, baseEnd_1855180] using wordTrace_append hprefix tailTrace_1855180
  have hstable : (prefixWord ++ tailWord_1855180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855180).length < 2 ^ (prefixWord ++ tailWord_1855180).sum := by decide
  have hdescent : baseEnd_1855180 < baseStart_1855180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855220 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1855220 : Nat := 118140960795 + 1855220 * 2 ^ 59
def prefixEnd_1855220 : Nat := 4983230072969 + 3 ^ 40 * 1855220 * 2
def baseEnd_1855220 : Nat := 952619579834336676918005

theorem tailTrace_1855220 : CollatzResearch.WordTrace tailWord_1855220 prefixEnd_1855220 952619579834336676918005 := by
  unfold tailWord_1855220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33832716169431130597841557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45110288225908174130455409 33832716169431130597841557)
  ·
    refine ⟨1585908570442084246773823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33832716169431130597841557 1585908570442084246773823)
    ·
      refine ⟨2378862855663126370160735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585908570442084246773823 2378862855663126370160735)
      ·
        refine ⟨3568294283494689555241103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378862855663126370160735 3568294283494689555241103)
        ·
          refine ⟨5352441425242034332861655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3568294283494689555241103 5352441425242034332861655)
          ·
            refine ⟨8028662137863051499292483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352441425242034332861655 8028662137863051499292483)
            ·
              refine ⟨12042993206794577248938725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8028662137863051499292483 12042993206794577248938725)
              ·
                refine ⟨2258061226273983234176011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12042993206794577248938725 2258061226273983234176011)
                ·
                  refine ⟨3387091839410974851264017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258061226273983234176011 3387091839410974851264017)
                  ·
                    refine ⟨2540318879558231138448013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387091839410974851264017 2540318879558231138448013)
                    ·
                      refine ⟨952619579834336676918005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2540318879558231138448013 952619579834336676918005)
                      ·
                        rfl

theorem cell23_1855220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1855220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855220 prefixEnd_1855220 := by exact prefixLift 1855220
  have htrace : WordTrace (prefixWord ++ tailWord_1855220) baseStart_1855220 baseEnd_1855220 := by
    simpa [prefixWord, tailWord_1855220, baseEnd_1855220] using wordTrace_append hprefix tailTrace_1855220
  have hstable : (prefixWord ++ tailWord_1855220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855220).length < 2 ^ (prefixWord ++ tailWord_1855220).sum := by decide
  have hdescent : baseEnd_1855220 < baseStart_1855220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855313 : List Nat := [1, 2, 2, 1, 5, 1, 4, 2, 5]
def baseStart_1855313 : Nat := 118140960795 + 1855313 * 2 ^ 59
def prefixEnd_1855313 : Nat := 4983230072969 + 3 ^ 40 * 1855313 * 2
def baseEnd_1855313 : Nat := 105851925948356090339453

theorem tailTrace_1855313 : CollatzResearch.WordTrace tailWord_1855313 prefixEnd_1855313 105851925948356090339453 := by
  unfold tailWord_1855313
  simp only [CollatzResearch.WordTrace]
  refine ⟨67668824327525338078818593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45112549551683558719212395 67668824327525338078818593)
  ·
    refine ⟨50751618245644003559113945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67668824327525338078818593 50751618245644003559113945)
    ·
      refine ⟨38063713684233002669335459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50751618245644003559113945 38063713684233002669335459)
      ·
        refine ⟨57095570526349504004003189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38063713684233002669335459 57095570526349504004003189)
        ·
          refine ⟨5352709736845266000375299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57095570526349504004003189 5352709736845266000375299)
          ·
            refine ⟨8029064605267899000562949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352709736845266000375299 8029064605267899000562949)
            ·
              refine ⟨1505449613487731062605553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8029064605267899000562949 1505449613487731062605553)
              ·
                refine ⟨1129087210115798296954165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505449613487731062605553 1129087210115798296954165)
                ·
                  refine ⟨105851925948356090339453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1129087210115798296954165 105851925948356090339453)
                  ·
                    rfl

theorem cell23_1855313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 5].length) (baseStart_1855313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855313 prefixEnd_1855313 := by exact prefixLift 1855313
  have htrace : WordTrace (prefixWord ++ tailWord_1855313) baseStart_1855313 baseEnd_1855313 := by
    simpa [prefixWord, tailWord_1855313, baseEnd_1855313] using wordTrace_append hprefix tailTrace_1855313
  have hstable : (prefixWord ++ tailWord_1855313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855313).length < 2 ^ (prefixWord ++ tailWord_1855313).sum := by decide
  have hdescent : baseEnd_1855313 < baseStart_1855313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855329 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1855329 : Nat := 118140960795 + 1855329 * 2 ^ 59
def prefixEnd_1855329 : Nat := 4983230072969 + 3 ^ 40 * 1855329 * 2
def baseEnd_1855329 : Nat := 952675549225676750455003

theorem tailTrace_1855329 : CollatzResearch.WordTrace tailWord_1855329 prefixEnd_1855329 952675549225676750455003 := by
  unfold tailWord_1855329
  simp only [CollatzResearch.WordTrace]
  refine ⟨67669407895467372811401041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45112938596978248540934027 67669407895467372811401041)
  ·
    refine ⟨50752055921600529608550781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67669407895467372811401041 50752055921600529608550781)
    ·
      refine ⟨19032020970600198603206543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50752055921600529608550781 19032020970600198603206543)
      ·
        refine ⟨28548031455900297904809815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19032020970600198603206543 28548031455900297904809815)
        ·
          refine ⟨42822047183850446857214723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28548031455900297904809815 42822047183850446857214723)
          ·
            refine ⟨64233070775775670285822085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42822047183850446857214723 64233070775775670285822085)
            ·
              refine ⟨12043700770457938178591641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64233070775775670285822085 12043700770457938178591641)
              ·
                refine ⟨9032775577843453633943731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12043700770457938178591641 9032775577843453633943731)
                ·
                  refine ⟨13549163366765180450915597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9032775577843453633943731 13549163366765180450915597)
                  ·
                    refine ⟨5080936262536942669093349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13549163366765180450915597 5080936262536942669093349)
                    ·
                      refine ⟨952675549225676750455003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5080936262536942669093349 952675549225676750455003)
                      ·
                        rfl

theorem cell23_1855329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1855329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855329 prefixEnd_1855329 := by exact prefixLift 1855329
  have htrace : WordTrace (prefixWord ++ tailWord_1855329) baseStart_1855329 baseEnd_1855329 := by
    simpa [prefixWord, tailWord_1855329, baseEnd_1855329] using wordTrace_append hprefix tailTrace_1855329
  have hstable : (prefixWord ++ tailWord_1855329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855329).length < 2 ^ (prefixWord ++ tailWord_1855329).sum := by decide
  have hdescent : baseEnd_1855329 < baseStart_1855329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855346 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_1855346 : Nat := 118140960795 + 1855346 * 2 ^ 59
def prefixEnd_1855346 : Nat := 4983230072969 + 3 ^ 40 * 1855346 * 2
def baseEnd_1855346 : Nat := 952684278396803183942425

theorem tailTrace_1855346 : CollatzResearch.WordTrace tailWord_1855346 prefixEnd_1855346 952684278396803183942425 := by
  unfold tailWord_1855346
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917506984101446178692473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45113351957603856476513261 16917506984101446178692473)
  ·
    refine ⟨12688130238076084634019355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16917506984101446178692473 12688130238076084634019355)
    ·
      refine ⟨19032195357114126951029033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12688130238076084634019355 19032195357114126951029033)
      ·
        refine ⟨14274146517835595213271775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19032195357114126951029033 14274146517835595213271775)
        ·
          refine ⟨21411219776753392819907663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14274146517835595213271775 21411219776753392819907663)
          ·
            refine ⟨32116829665130089229861495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21411219776753392819907663 32116829665130089229861495)
            ·
              refine ⟨48175244497695133844792243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32116829665130089229861495 48175244497695133844792243)
              ·
                refine ⟨72262866746542700767188365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48175244497695133844792243 72262866746542700767188365)
                ·
                  refine ⟨27098575029953512787695637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72262866746542700767188365 27098575029953512787695637)
                  ·
                    refine ⟨1270245704529070911923233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27098575029953512787695637 1270245704529070911923233)
                    ·
                      refine ⟨952684278396803183942425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270245704529070911923233 952684278396803183942425)
                      ·
                        rfl

theorem cell23_1855346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_1855346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855346 prefixEnd_1855346 := by exact prefixLift 1855346
  have htrace : WordTrace (prefixWord ++ tailWord_1855346) baseStart_1855346 baseEnd_1855346 := by
    simpa [prefixWord, tailWord_1855346, baseEnd_1855346] using wordTrace_append hprefix tailTrace_1855346
  have hstable : (prefixWord ++ tailWord_1855346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855346).length < 2 ^ (prefixWord ++ tailWord_1855346).sum := by decide
  have hdescent : baseEnd_1855346 < baseStart_1855346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855369 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 8]
def baseStart_1855369 : Nat := 118140960795 + 1855369 * 2 ^ 59
def prefixEnd_1855369 : Nat := 4983230072969 + 3 ^ 40 * 1855369 * 2
def baseEnd_1855369 : Nat := 105855120939095177106091

theorem tailTrace_1855369 : CollatzResearch.WordTrace tailWord_1855369 prefixEnd_1855369 105855120939095177106091 := by
  unfold tailWord_1855369
  simp only [CollatzResearch.WordTrace]
  refine ⟨67670866815322459642857161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45113911210214973095238107 67670866815322459642857161)
  ·
    refine ⟨50753150111491844732142871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67670866815322459642857161 50753150111491844732142871)
    ·
      refine ⟨76129725167237767098214307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50753150111491844732142871 76129725167237767098214307)
      ·
        refine ⟨114194587750856650647321461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76129725167237767098214307 114194587750856650647321461)
        ·
          refine ⟨10705742601642810998186387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114194587750856650647321461 10705742601642810998186387)
          ·
            refine ⟨16058613902464216497279581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10705742601642810998186387 16058613902464216497279581)
            ·
              refine ⟨6021980213424081186479843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16058613902464216497279581 6021980213424081186479843)
              ·
                refine ⟨9032970320136121779719765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021980213424081186479843 9032970320136121779719765)
                ·
                  refine ⟨105855120939095177106091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9032970320136121779719765 105855120939095177106091)
                  ·
                    rfl

theorem cell23_1855369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_1855369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855369 prefixEnd_1855369 := by exact prefixLift 1855369
  have htrace : WordTrace (prefixWord ++ tailWord_1855369) baseStart_1855369 baseEnd_1855369 := by
    simpa [prefixWord, tailWord_1855369, baseEnd_1855369] using wordTrace_append hprefix tailTrace_1855369
  have hstable : (prefixWord ++ tailWord_1855369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855369).length < 2 ^ (prefixWord ++ tailWord_1855369).sum := by decide
  have hdescent : baseEnd_1855369 < baseStart_1855369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855416 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 1, 5]
def baseStart_1855416 : Nat := 118140960795 + 1855416 * 2 ^ 59
def prefixEnd_1855416 : Nat := 4983230072969 + 3 ^ 40 * 1855416 * 2
def baseEnd_1855416 : Nat := 317573407347539303355701

theorem tailTrace_1855416 : CollatzResearch.WordTrace tailWord_1855416 prefixEnd_1855416 317573407347539303355701 := by
  unfold tailWord_1855416
  simp only [CollatzResearch.WordTrace]
  refine ⟨33836290523076093334909051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45115054030768124446545401 33836290523076093334909051)
  ·
    refine ⟨50754435784614140002363577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33836290523076093334909051 50754435784614140002363577)
    ·
      refine ⟨38065826838460605001772683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50754435784614140002363577 38065826838460605001772683)
      ·
        refine ⟨57098740257690907502659025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38065826838460605001772683 57098740257690907502659025)
        ·
          refine ⟨42824055193268180626994269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57098740257690907502659025 42824055193268180626994269)
          ·
            refine ⟨16059020697475567735122851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42824055193268180626994269 16059020697475567735122851)
            ·
              refine ⟨24088531046213351602684277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16059020697475567735122851 24088531046213351602684277)
              ·
                refine ⟨2258299785582501712751651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24088531046213351602684277 2258299785582501712751651)
                ·
                  refine ⟨3387449678373752569127477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258299785582501712751651 3387449678373752569127477)
                  ·
                    refine ⟨317573407347539303355701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3387449678373752569127477 317573407347539303355701)
                    ·
                      rfl

theorem cell23_1855416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_1855416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855416 prefixEnd_1855416 := by exact prefixLift 1855416
  have htrace : WordTrace (prefixWord ++ tailWord_1855416) baseStart_1855416 baseEnd_1855416 := by
    simpa [prefixWord, tailWord_1855416, baseEnd_1855416] using wordTrace_append hprefix tailTrace_1855416
  have hstable : (prefixWord ++ tailWord_1855416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855416).length < 2 ^ (prefixWord ++ tailWord_1855416).sum := by decide
  have hdescent : baseEnd_1855416 < baseStart_1855416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855423 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 2, 3, 2]
def baseStart_1855423 : Nat := 118140960795 + 1855423 * 2 ^ 59
def prefixEnd_1855423 : Nat := 4983230072969 + 3 ^ 40 * 1855423 * 2
def baseEnd_1855423 : Nat := 952723816407199382679571

theorem tailTrace_1855423 : CollatzResearch.WordTrace tailWord_1855423 prefixEnd_1855423 952723816407199382679571 := by
  unfold tailWord_1855423
  simp only [CollatzResearch.WordTrace]
  refine ⟨67672836357126826865322923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45115224238084551243548615 67672836357126826865322923)
  ·
    refine ⟨101509254535690240297984385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67672836357126826865322923 101509254535690240297984385)
    ·
      refine ⟨76131940901767680223488289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101509254535690240297984385 76131940901767680223488289)
      ·
        refine ⟨57098955676325760167616217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76131940901767680223488289 57098955676325760167616217)
        ·
          refine ⟨42824216757244320125712163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57098955676325760167616217 42824216757244320125712163)
          ·
            refine ⟨64236325135866480188568245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42824216757244320125712163 64236325135866480188568245)
            ·
              refine ⟨6022155481487482517678273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64236325135866480188568245 6022155481487482517678273)
              ·
                refine ⟨4516616611115611888258705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6022155481487482517678273 4516616611115611888258705)
                ·
                  refine ⟨3387462458336708916194029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516616611115611888258705 3387462458336708916194029)
                  ·
                    refine ⟨1270298421876265843572761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387462458336708916194029 1270298421876265843572761)
                    ·
                      refine ⟨952723816407199382679571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270298421876265843572761 952723816407199382679571)
                      ·
                        rfl

theorem cell23_1855423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3, 2].length) (baseStart_1855423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855423 prefixEnd_1855423 := by exact prefixLift 1855423
  have htrace : WordTrace (prefixWord ++ tailWord_1855423) baseStart_1855423 baseEnd_1855423 := by
    simpa [prefixWord, tailWord_1855423, baseEnd_1855423] using wordTrace_append hprefix tailTrace_1855423
  have hstable : (prefixWord ++ tailWord_1855423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855423).length < 2 ^ (prefixWord ++ tailWord_1855423).sum := by decide
  have hdescent : baseEnd_1855423 < baseStart_1855423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855429 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_1855429 : Nat := 118140960795 + 1855429 * 2 ^ 59
def prefixEnd_1855429 : Nat := 4983230072969 + 3 ^ 40 * 1855429 * 2
def baseEnd_1855429 : Nat := 317575632430375453068181

theorem tailTrace_1855429 : CollatzResearch.WordTrace tailWord_1855429 prefixEnd_1855429 317575632430375453068181 := by
  unfold tailWord_1855429
  simp only [CollatzResearch.WordTrace]
  refine ⟨67673055195105089890041341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45115370130070059926694227 67673055195105089890041341)
  ·
    refine ⟨25377395698164408708765503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67673055195105089890041341 25377395698164408708765503)
    ·
      refine ⟨38066093547246613063148255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25377395698164408708765503 38066093547246613063148255)
      ·
        refine ⟨57099140320869919594722383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38066093547246613063148255 57099140320869919594722383)
        ·
          refine ⟨85648710481304879392083575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57099140320869919594722383 85648710481304879392083575)
          ·
            refine ⟨128473065721957319088125363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85648710481304879392083575 128473065721957319088125363)
            ·
              refine ⟨192709598582935978632188045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128473065721957319088125363 192709598582935978632188045)
              ·
                refine ⟨72266099468600991987070517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192709598582935978632188045 72266099468600991987070517)
                ·
                  refine ⟨6774946825181342998787861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72266099468600991987070517 6774946825181342998787861)
                  ·
                    refine ⟨317575632430375453068181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6774946825181342998787861 317575632430375453068181)
                    ·
                      rfl

theorem cell23_1855429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_1855429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855429 prefixEnd_1855429 := by exact prefixLift 1855429
  have htrace : WordTrace (prefixWord ++ tailWord_1855429) baseStart_1855429 baseEnd_1855429 := by
    simpa [prefixWord, tailWord_1855429, baseEnd_1855429] using wordTrace_append hprefix tailTrace_1855429
  have hstable : (prefixWord ++ tailWord_1855429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855429).length < 2 ^ (prefixWord ++ tailWord_1855429).sum := by decide
  have hdescent : baseEnd_1855429 < baseStart_1855429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855450 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_1855450 : Nat := 118140960795 + 1855450 * 2 ^ 59
def prefixEnd_1855450 : Nat := 4983230072969 + 3 ^ 40 * 1855450 * 2
def baseEnd_1855450 : Nat := 317579226794956925680649

theorem tailTrace_1855450 : CollatzResearch.WordTrace tailWord_1855450 prefixEnd_1855450 317579226794956925680649 := by
  unfold tailWord_1855450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16918455282007252619138951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45115880752019340317703869 16918455282007252619138951)
  ·
    refine ⟨25377682923010878928708427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16918455282007252619138951 25377682923010878928708427)
    ·
      refine ⟨38066524384516318393062641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25377682923010878928708427 38066524384516318393062641)
      ·
        refine ⟨28549893288387238794796981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38066524384516318393062641 28549893288387238794796981)
        ·
          refine ⟨2676552495786303637012217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28549893288387238794796981 2676552495786303637012217)
          ·
            refine ⟨2007414371839727727759163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2676552495786303637012217 2007414371839727727759163)
            ·
              refine ⟨3011121557759591591638745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007414371839727727759163 3011121557759591591638745)
              ·
                refine ⟨2258341168319693693729059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011121557759591591638745 2258341168319693693729059)
                ·
                  refine ⟨3387511752479540540593589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258341168319693693729059 3387511752479540540593589)
                  ·
                    refine ⟨317579226794956925680649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3387511752479540540593589 317579226794956925680649)
                    ·
                      rfl

theorem cell23_1855450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_1855450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855450 prefixEnd_1855450 := by exact prefixLift 1855450
  have htrace : WordTrace (prefixWord ++ tailWord_1855450) baseStart_1855450 baseEnd_1855450 := by
    simpa [prefixWord, tailWord_1855450, baseEnd_1855450] using wordTrace_append hprefix tailTrace_1855450
  have hstable : (prefixWord ++ tailWord_1855450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855450).length < 2 ^ (prefixWord ++ tailWord_1855450).sum := by decide
  have hdescent : baseEnd_1855450 < baseStart_1855450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855463 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 1, 6]
def baseStart_1855463 : Nat := 118140960795 + 1855463 * 2 ^ 59
def prefixEnd_1855463 : Nat := 4983230072969 + 3 ^ 40 * 1855463 * 2
def baseEnd_1855463 : Nat := 317581451877793075393129

theorem tailTrace_1855463 : CollatzResearch.WordTrace tailWord_1855463 prefixEnd_1855463 317581451877793075393129 := by
  unfold tailWord_1855463
  simp only [CollatzResearch.WordTrace]
  refine ⟨67674295276981913696779043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45116196851321275797852695 67674295276981913696779043)
  ·
    refine ⟨101511442915472870545168565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67674295276981913696779043 101511442915472870545168565)
    ·
      refine ⟨9516697773325581613609553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101511442915472870545168565 9516697773325581613609553)
      ·
        refine ⟨7137523329994186210207165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9516697773325581613609553 7137523329994186210207165)
        ·
          refine ⟨2676571248747819828827687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7137523329994186210207165 2676571248747819828827687)
          ·
            refine ⟨4014856873121729743241531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676571248747819828827687 4014856873121729743241531)
            ·
              refine ⟨6022285309682594614862297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014856873121729743241531 6022285309682594614862297)
              ·
                refine ⟨4516713982261945961146723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6022285309682594614862297 4516713982261945961146723)
                ·
                  refine ⟨6775070973392918941720085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4516713982261945961146723 6775070973392918941720085)
                  ·
                    refine ⟨317581451877793075393129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6775070973392918941720085 317581451877793075393129)
                    ·
                      rfl

theorem cell23_1855463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_1855463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855463 prefixEnd_1855463 := by exact prefixLift 1855463
  have htrace : WordTrace (prefixWord ++ tailWord_1855463) baseStart_1855463 baseEnd_1855463 := by
    simpa [prefixWord, tailWord_1855463, baseEnd_1855463] using wordTrace_append hprefix tailTrace_1855463
  have hstable : (prefixWord ++ tailWord_1855463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855463).length < 2 ^ (prefixWord ++ tailWord_1855463).sum := by decide
  have hdescent : baseEnd_1855463 < baseStart_1855463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855479 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1855479 : Nat := 118140960795 + 1855479 * 2 ^ 59
def prefixEnd_1855479 : Nat := 4983230072969 + 3 ^ 40 * 1855479 * 2
def baseEnd_1855479 : Nat := 952752571323851163579313

theorem tailTrace_1855479 : CollatzResearch.WordTrace tailWord_1855479 prefixEnd_1855479 952752571323851163579313 := by
  unfold tailWord_1855479
  simp only [CollatzResearch.WordTrace]
  refine ⟨67674878844923948429361491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45116585896615965619574327 67674878844923948429361491)
  ·
    refine ⟨101512318267385922644042237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67674878844923948429361491 101512318267385922644042237)
    ·
      refine ⟨38067119350269720991515839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101512318267385922644042237 38067119350269720991515839)
      ·
        refine ⟨57100679025404581487273759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38067119350269720991515839 57100679025404581487273759)
        ·
          refine ⟨85651018538106872230910639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57100679025404581487273759 85651018538106872230910639)
          ·
            refine ⟨128476527807160308346365959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85651018538106872230910639 128476527807160308346365959)
            ·
              refine ⟨192714791710740462519548939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128476527807160308346365959 192714791710740462519548939)
              ·
                refine ⟨289072187566110693779323409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192714791710740462519548939 289072187566110693779323409)
                ·
                  refine ⟨216804140674583020334492557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289072187566110693779323409 216804140674583020334492557)
                  ·
                    refine ⟨81301552752968632625434709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216804140674583020334492557 81301552752968632625434709)
                    ·
                      refine ⟨952752571323851163579313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 81301552752968632625434709 952752571323851163579313)
                      ·
                        rfl

theorem cell23_1855479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1855479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855479 prefixEnd_1855479 := by exact prefixLift 1855479
  have htrace : WordTrace (prefixWord ++ tailWord_1855479) baseStart_1855479 baseEnd_1855479 := by
    simpa [prefixWord, tailWord_1855479, baseEnd_1855479] using wordTrace_append hprefix tailTrace_1855479
  have hstable : (prefixWord ++ tailWord_1855479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855479).length < 2 ^ (prefixWord ++ tailWord_1855479).sum := by decide
  have hdescent : baseEnd_1855479 < baseStart_1855479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855524 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_1855524 : Nat := 118140960795 + 1855524 * 2 ^ 59
def prefixEnd_1855524 : Nat := 4983230072969 + 3 ^ 40 * 1855524 * 2
def baseEnd_1855524 : Nat := 952775677953303487516607

theorem tailTrace_1855524 : CollatzResearch.WordTrace tailWord_1855524 prefixEnd_1855524 952775677953303487516607 := by
  unfold tailWord_1855524
  simp only [CollatzResearch.WordTrace]
  refine ⟨33838260064880460557374813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45117680086507280743166417 33838260064880460557374813)
  ·
    refine ⟨12689347524330172709015555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33838260064880460557374813 12689347524330172709015555)
    ·
      refine ⟨19034021286495259063523333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12689347524330172709015555 19034021286495259063523333)
      ·
        refine ⟨3568878991217861074410625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19034021286495259063523333 3568878991217861074410625)
        ·
          refine ⟨2676659243413395805807969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3568878991217861074410625 2676659243413395805807969)
          ·
            refine ⟨2007494432560046854355977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2676659243413395805807969 2007494432560046854355977)
            ·
              refine ⟨1505620824420035140766983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007494432560046854355977 1505620824420035140766983)
              ·
                refine ⟨2258431236630052711150475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505620824420035140766983 2258431236630052711150475)
                ·
                  refine ⟨3387646854945079066725713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258431236630052711150475 3387646854945079066725713)
                  ·
                    refine ⟨2540735141208809300044285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387646854945079066725713 2540735141208809300044285)
                    ·
                      refine ⟨952775677953303487516607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2540735141208809300044285 952775677953303487516607)
                      ·
                        rfl

theorem cell23_1855524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_1855524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855524 prefixEnd_1855524 := by exact prefixLift 1855524
  have htrace : WordTrace (prefixWord ++ tailWord_1855524) baseStart_1855524 baseEnd_1855524 := by
    simpa [prefixWord, tailWord_1855524, baseEnd_1855524] using wordTrace_append hprefix tailTrace_1855524
  have hstable : (prefixWord ++ tailWord_1855524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855524).length < 2 ^ (prefixWord ++ tailWord_1855524).sum := by decide
  have hdescent : baseEnd_1855524 < baseStart_1855524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855536 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 2, 6]
def baseStart_1855536 : Nat := 118140960795 + 1855536 * 2 ^ 59
def prefixEnd_1855536 : Nat := 4983230072969 + 3 ^ 40 * 1855536 * 2
def baseEnd_1855536 : Nat := 317593946573719146855517

theorem tailTrace_1855536 : CollatzResearch.WordTrace tailWord_1855536 prefixEnd_1855536 317593946573719146855517 := by
  unfold tailWord_1855536
  simp only [CollatzResearch.WordTrace]
  refine ⟨33838478902858723582093231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45117971870478298109457641 33838478902858723582093231)
  ·
    refine ⟨50757718354288085373139847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33838478902858723582093231 50757718354288085373139847)
    ·
      refine ⟨76136577531432128059709771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50757718354288085373139847 76136577531432128059709771)
      ·
        refine ⟨114204866297148192089564657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76136577531432128059709771 114204866297148192089564657)
        ·
          refine ⟨85653649722861144067173493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114204866297148192089564657 85653649722861144067173493)
          ·
            refine ⟨8030029661518232256297515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85653649722861144067173493 8030029661518232256297515)
            ·
              refine ⟨12045044492277348384446273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030029661518232256297515 12045044492277348384446273)
              ·
                refine ⟨9033783369208011288334705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12045044492277348384446273 9033783369208011288334705)
                ·
                  refine ⟨6775337526906008466251029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033783369208011288334705 6775337526906008466251029)
                  ·
                    refine ⟨317593946573719146855517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6775337526906008466251029 317593946573719146855517)
                    ·
                      rfl

theorem cell23_1855536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_1855536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855536 prefixEnd_1855536 := by exact prefixLift 1855536
  have htrace : WordTrace (prefixWord ++ tailWord_1855536) baseStart_1855536 baseEnd_1855536 := by
    simpa [prefixWord, tailWord_1855536, baseEnd_1855536] using wordTrace_append hprefix tailTrace_1855536
  have hstable : (prefixWord ++ tailWord_1855536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855536).length < 2 ^ (prefixWord ++ tailWord_1855536).sum := by decide
  have hdescent : baseEnd_1855536 < baseStart_1855536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855537 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 3]
def baseStart_1855537 : Nat := 118140960795 + 1855537 * 2 ^ 59
def prefixEnd_1855537 : Nat := 4983230072969 + 3 ^ 40 * 1855537 * 2
def baseEnd_1855537 : Nat := 952782353201811936654047

theorem tailTrace_1855537 : CollatzResearch.WordTrace tailWord_1855537 prefixEnd_1855537 952782353201811936654047 := by
  unfold tailWord_1855537
  simp only [CollatzResearch.WordTrace]
  refine ⟨67676994278713824334972865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45117996185809216223315243 67676994278713824334972865)
  ·
    refine ⟨50757745709035368251229649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67676994278713824334972865 50757745709035368251229649)
    ·
      refine ⟨38068309281776526188422237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50757745709035368251229649 38068309281776526188422237)
      ·
        refine ⟨14275615980666197320658339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38068309281776526188422237 14275615980666197320658339)
        ·
          refine ⟨21413423970999295980987509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14275615980666197320658339 21413423970999295980987509)
          ·
            refine ⟨2007508497281183998217579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21413423970999295980987509 2007508497281183998217579)
            ·
              refine ⟨3011262745921775997326369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007508497281183998217579 3011262745921775997326369)
              ·
                refine ⟨2258447059441331997994777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011262745921775997326369 2258447059441331997994777)
                ·
                  refine ⟨1693835294580998998496083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2258447059441331997994777 1693835294580998998496083)
                  ·
                    refine ⟨2540752941871498497744125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1693835294580998998496083 2540752941871498497744125)
                    ·
                      refine ⟨952782353201811936654047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2540752941871498497744125 952782353201811936654047)
                      ·
                        rfl

theorem cell23_1855537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_1855537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855537 prefixEnd_1855537 := by exact prefixLift 1855537
  have htrace : WordTrace (prefixWord ++ tailWord_1855537) baseStart_1855537 baseEnd_1855537 := by
    simpa [prefixWord, tailWord_1855537, baseEnd_1855537] using wordTrace_append hprefix tailTrace_1855537
  have hstable : (prefixWord ++ tailWord_1855537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855537).length < 2 ^ (prefixWord ++ tailWord_1855537).sum := by decide
  have hdescent : baseEnd_1855537 < baseStart_1855537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855543 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 3, 4, 2]
def baseStart_1855543 : Nat := 118140960795 + 1855543 * 2 ^ 59
def prefixEnd_1855543 : Nat := 4983230072969 + 3 ^ 40 * 1855543 * 2
def baseEnd_1855543 : Nat := 952785434085738913179019

theorem tailTrace_1855543 : CollatzResearch.WordTrace tailWord_1855543 prefixEnd_1855543 952785434085738913179019 := by
  unfold tailWord_1855543
  simp only [CollatzResearch.WordTrace]
  refine ⟨67677213116692087359691283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45118142077794724906460855 67677213116692087359691283)
  ·
    refine ⟨101515819675038131039536925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67677213116692087359691283 101515819675038131039536925)
    ·
      refine ⟨38068432378139299139826347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101515819675038131039536925 38068432378139299139826347)
      ·
        refine ⟨57102648567208948709739521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38068432378139299139826347 57102648567208948709739521)
        ·
          refine ⟨42826986425406711532304641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57102648567208948709739521 42826986425406711532304641)
          ·
            refine ⟨32120239819055033649228481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42826986425406711532304641 32120239819055033649228481)
            ·
              refine ⟨24090179864291275236921361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32120239819055033649228481 24090179864291275236921361)
              ·
                refine ⟨18067634898218456427691021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24090179864291275236921361 18067634898218456427691021)
                ·
                  refine ⟨6775363086831921160384133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18067634898218456427691021 6775363086831921160384133)
                  ·
                    refine ⟨1270380578780985217572025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775363086831921160384133 1270380578780985217572025)
                    ·
                      refine ⟨952785434085738913179019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270380578780985217572025 952785434085738913179019)
                      ·
                        rfl

theorem cell23_1855543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_1855543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855543 prefixEnd_1855543 := by exact prefixLift 1855543
  have htrace : WordTrace (prefixWord ++ tailWord_1855543) baseStart_1855543 baseEnd_1855543 := by
    simpa [prefixWord, tailWord_1855543, baseEnd_1855543] using wordTrace_append hprefix tailTrace_1855543
  have hstable : (prefixWord ++ tailWord_1855543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855543).length < 2 ^ (prefixWord ++ tailWord_1855543).sum := by decide
  have hdescent : baseEnd_1855543 < baseStart_1855543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855546 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1855546 : Nat := 118140960795 + 1855546 * 2 ^ 59
def prefixEnd_1855546 : Nat := 4983230072969 + 3 ^ 40 * 1855546 * 2
def baseEnd_1855546 : Nat := 952786974527702401441505

theorem tailTrace_1855546 : CollatzResearch.WordTrace tailWord_1855546 prefixEnd_1855546 952786974527702401441505 := by
  unfold tailWord_1855546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919330633920304718012623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45118215023787479248033661 16919330633920304718012623)
  ·
    refine ⟨25378995950880457077018935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16919330633920304718012623 25378995950880457077018935)
    ·
      refine ⟨38068493926320685615528403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25378995950880457077018935 38068493926320685615528403)
      ·
        refine ⟨57102740889481028423292605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38068493926320685615528403 57102740889481028423292605)
        ·
          refine ⟨21413527833555385658734727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57102740889481028423292605 21413527833555385658734727)
          ·
            refine ⟨32120291750333078488102091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21413527833555385658734727 32120291750333078488102091)
            ·
              refine ⟨48180437625499617732153137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32120291750333078488102091 48180437625499617732153137)
              ·
                refine ⟨36135328219124713299114853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48180437625499617732153137 36135328219124713299114853)
                ·
                  refine ⟨6775374041085883743584035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36135328219124713299114853 6775374041085883743584035)
                  ·
                    refine ⟨10163061061628825615376053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6775374041085883743584035 10163061061628825615376053)
                    ·
                      refine ⟨952786974527702401441505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10163061061628825615376053 952786974527702401441505)
                      ·
                        rfl

theorem cell23_1855546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1855546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855546 prefixEnd_1855546 := by exact prefixLift 1855546
  have htrace : WordTrace (prefixWord ++ tailWord_1855546) baseStart_1855546 baseEnd_1855546 := by
    simpa [prefixWord, tailWord_1855546, baseEnd_1855546] using wordTrace_append hprefix tailTrace_1855546
  have hstable : (prefixWord ++ tailWord_1855546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855546).length < 2 ^ (prefixWord ++ tailWord_1855546).sum := by decide
  have hdescent : baseEnd_1855546 < baseStart_1855546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855553 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1855553 : Nat := 118140960795 + 1855553 * 2 ^ 59
def prefixEnd_1855553 : Nat := 4983230072969 + 3 ^ 40 * 1855553 * 2
def baseEnd_1855553 : Nat := 317596856297427958017991

theorem tailTrace_1855553 : CollatzResearch.WordTrace tailWord_1855553 prefixEnd_1855553 317596856297427958017991 := by
  unfold tailWord_1855553
  simp only [CollatzResearch.WordTrace]
  refine ⟨67677577846655859067555313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45118385231103906045036875 67677577846655859067555313)
  ·
    refine ⟨50758183384991894300666485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67677577846655859067555313 50758183384991894300666485)
    ·
      refine ⟨4758579692342990090687483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50758183384991894300666485 4758579692342990090687483)
      ·
        refine ⟨7137869538514485136031225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758579692342990090687483 7137869538514485136031225)
        ·
          refine ⟨5353402153885863852023419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7137869538514485136031225 5353402153885863852023419)
          ·
            refine ⟨8030103230828795778035129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353402153885863852023419 8030103230828795778035129)
            ·
              refine ⟨6022577423121596833526347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8030103230828795778035129 6022577423121596833526347)
              ·
                refine ⟨9033866134682395250289521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6022577423121596833526347 9033866134682395250289521)
                ·
                  refine ⟨6775399601011796437717141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033866134682395250289521 6775399601011796437717141)
                  ·
                    refine ⟨317596856297427958017991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6775399601011796437717141 317596856297427958017991)
                    ·
                      rfl

theorem cell23_1855553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1855553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855553 prefixEnd_1855553 := by exact prefixLift 1855553
  have htrace : WordTrace (prefixWord ++ tailWord_1855553) baseStart_1855553 baseEnd_1855553 := by
    simpa [prefixWord, tailWord_1855553, baseEnd_1855553] using wordTrace_append hprefix tailTrace_1855553
  have hstable : (prefixWord ++ tailWord_1855553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855553).length < 2 ^ (prefixWord ++ tailWord_1855553).sum := by decide
  have hdescent : baseEnd_1855553 < baseStart_1855553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855583 : List Nat := [1, 1, 2, 3, 1, 1, 2, 7, 5]
def baseStart_1855583 : Nat := 118140960795 + 1855583 * 2 ^ 59
def prefixEnd_1855583 : Nat := 4983230072969 + 3 ^ 40 * 1855583 * 2
def baseEnd_1855583 : Nat := 105867330367990972964315

theorem tailTrace_1855583 : CollatzResearch.WordTrace tailWord_1855583 prefixEnd_1855583 105867330367990972964315 := by
  unfold tailWord_1855583
  simp only [CollatzResearch.WordTrace]
  refine ⟨67678672036547174191147403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45119114691031449460764935 67678672036547174191147403)
  ·
    refine ⟨101518008054820761286721105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67678672036547174191147403 101518008054820761286721105)
    ·
      refine ⟨76138506041115570965040829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101518008054820761286721105 76138506041115570965040829)
      ·
        refine ⟨28551939765418339111890311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76138506041115570965040829 28551939765418339111890311)
        ·
          refine ⟨42827909648127508667835467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28551939765418339111890311 42827909648127508667835467)
          ·
            refine ⟨64241864472191263001753201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42827909648127508667835467 64241864472191263001753201)
            ·
              refine ⟨48181398354143447251314901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64241864472191263001753201 48181398354143447251314901)
              ·
                refine ⟨1129251523925237044952693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48181398354143447251314901 1129251523925237044952693)
                ·
                  refine ⟨105867330367990972964315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1129251523925237044952693 105867330367990972964315)
                  ·
                    rfl

theorem cell23_1855583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 5].length) (baseStart_1855583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855583 prefixEnd_1855583 := by exact prefixLift 1855583
  have htrace : WordTrace (prefixWord ++ tailWord_1855583) baseStart_1855583 baseEnd_1855583 := by
    simpa [prefixWord, tailWord_1855583, baseEnd_1855583] using wordTrace_append hprefix tailTrace_1855583
  have hstable : (prefixWord ++ tailWord_1855583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855583).length < 2 ^ (prefixWord ++ tailWord_1855583).sum := by decide
  have hdescent : baseEnd_1855583 < baseStart_1855583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855673 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 6]
def baseStart_1855673 : Nat := 118140960795 + 1855673 * 2 ^ 59
def prefixEnd_1855673 : Nat := 4983230072969 + 3 ^ 40 * 1855673 * 2
def baseEnd_1855673 : Nat := 105872465174535933839269

theorem tailTrace_1855673 : CollatzResearch.WordTrace tailWord_1855673 prefixEnd_1855673 105872465174535933839269 := by
  unfold tailWord_1855673
  simp only [CollatzResearch.WordTrace]
  refine ⟨67681954606221119561923673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45121303070814079707949115 67681954606221119561923673)
  ·
    refine ⟨50761465954665839671442755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67681954606221119561923673 50761465954665839671442755)
    ·
      refine ⟨76142198931998759507164133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50761465954665839671442755 76142198931998759507164133)
      ·
        refine ⟨14276662299749767407593275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76142198931998759507164133 14276662299749767407593275)
        ·
          refine ⟨21414993449624651111389913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14276662299749767407593275 21414993449624651111389913)
          ·
            refine ⟨16061245087218488333542435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21414993449624651111389913 16061245087218488333542435)
            ·
              refine ⟨24091867630827732500313653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16061245087218488333542435 24091867630827732500313653)
              ·
                refine ⟨2258612590390099921904405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24091867630827732500313653 2258612590390099921904405)
                ·
                  refine ⟨105872465174535933839269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2258612590390099921904405 105872465174535933839269)
                  ·
                    rfl

theorem cell23_1855673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 6].length) (baseStart_1855673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855673 prefixEnd_1855673 := by exact prefixLift 1855673
  have htrace : WordTrace (prefixWord ++ tailWord_1855673) baseStart_1855673 baseEnd_1855673 := by
    simpa [prefixWord, tailWord_1855673, baseEnd_1855673] using wordTrace_append hprefix tailTrace_1855673
  have hstable : (prefixWord ++ tailWord_1855673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855673).length < 2 ^ (prefixWord ++ tailWord_1855673).sum := by decide
  have hdescent : baseEnd_1855673 < baseStart_1855673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855694 : List Nat := [4, 1, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_1855694 : Nat := 118140960795 + 1855694 * 2 ^ 59
def prefixEnd_1855694 : Nat := 4983230072969 + 3 ^ 40 * 1855694 * 2
def baseEnd_1855694 : Nat := 317620989888189274130275

theorem tailTrace_1855694 : CollatzResearch.WordTrace tailWord_1855694 prefixEnd_1855694 317620989888189274130275 := by
  unfold tailWord_1855694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460340067393130018554767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45121813692763360098958757 8460340067393130018554767)
  ·
    refine ⟨12690510101089695027832151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8460340067393130018554767 12690510101089695027832151)
    ·
      refine ⟨19035765151634542541748227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12690510101089695027832151 19035765151634542541748227)
      ·
        refine ⟨28553647727451813812622341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19035765151634542541748227 28553647727451813812622341)
        ·
          refine ⟨5353808948897215089866689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28553647727451813812622341 5353808948897215089866689)
          ·
            refine ⟨4015356711672911317400017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5353808948897215089866689 4015356711672911317400017)
            ·
              refine ⟨3011517533754683488050013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015356711672911317400017 3011517533754683488050013)
              ·
                refine ⟨1129319075158006308018755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3011517533754683488050013 1129319075158006308018755)
                ·
                  refine ⟨1693978612737009462028133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129319075158006308018755 1693978612737009462028133)
                  ·
                    refine ⟨317620989888189274130275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1693978612737009462028133 317620989888189274130275)
                    ·
                      rfl

theorem cell23_1855694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_1855694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855694 prefixEnd_1855694 := by exact prefixLift 1855694
  have htrace : WordTrace (prefixWord ++ tailWord_1855694) baseStart_1855694 baseEnd_1855694 := by
    simpa [prefixWord, tailWord_1855694, baseEnd_1855694] using wordTrace_append hprefix tailTrace_1855694
  have hstable : (prefixWord ++ tailWord_1855694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855694).length < 2 ^ (prefixWord ++ tailWord_1855694).sum := by decide
  have hdescent : baseEnd_1855694 < baseStart_1855694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855717 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1855717 : Nat := 118140960795 + 1855717 * 2 ^ 59
def prefixEnd_1855717 : Nat := 4983230072969 + 3 ^ 40 * 1855717 * 2
def baseEnd_1855717 : Nat := 952874779719621232403219

theorem tailTrace_1855717 : CollatzResearch.WordTrace tailWord_1855717 prefixEnd_1855717 952874779719621232403219 := by
  unfold tailWord_1855717
  simp only [CollatzResearch.WordTrace]
  refine ⟨67683559418061715076525405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45122372945374476717683603 67683559418061715076525405)
  ·
    refine ⟨25381334781773143153697027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67683559418061715076525405 25381334781773143153697027)
    ·
      refine ⟨38072002172659714730545541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25381334781773143153697027 38072002172659714730545541)
      ·
        refine ⟨7138500407373696511977289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38072002172659714730545541 7138500407373696511977289)
        ·
          refine ⟨5353875305530272383982967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7138500407373696511977289 5353875305530272383982967)
          ·
            refine ⟨8030812958295408575974451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353875305530272383982967 8030812958295408575974451)
            ·
              refine ⟨12046219437443112863961677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030812958295408575974451 12046219437443112863961677)
              ·
                refine ⟨4517332289041167323985629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12046219437443112863961677 4517332289041167323985629)
                ·
                  refine ⟨1693999608390437746494611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4517332289041167323985629 1693999608390437746494611)
                  ·
                    refine ⟨2540999412585656619741917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1693999608390437746494611 2540999412585656619741917)
                    ·
                      refine ⟨952874779719621232403219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2540999412585656619741917 952874779719621232403219)
                      ·
                        rfl

theorem cell23_1855717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1855717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855717 prefixEnd_1855717 := by exact prefixLift 1855717
  have htrace : WordTrace (prefixWord ++ tailWord_1855717) baseStart_1855717 baseEnd_1855717 := by
    simpa [prefixWord, tailWord_1855717, baseEnd_1855717] using wordTrace_append hprefix tailTrace_1855717
  have hstable : (prefixWord ++ tailWord_1855717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855717).length < 2 ^ (prefixWord ++ tailWord_1855717).sum := by decide
  have hdescent : baseEnd_1855717 < baseStart_1855717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855743 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_1855743 : Nat := 118140960795 + 1855743 * 2 ^ 59
def prefixEnd_1855743 : Nat := 4983230072969 + 3 ^ 40 * 1855743 * 2
def baseEnd_1855743 : Nat := 952888130216638130678099

theorem tailTrace_1855743 : CollatzResearch.WordTrace tailWord_1855743 prefixEnd_1855743 952888130216638130678099 := by
  unfold tailWord_1855743
  simp only [CollatzResearch.WordTrace]
  refine ⟨67684507715967521516971883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45123005143978347677981255 67684507715967521516971883)
  ·
    refine ⟨101526761573951282275457825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67684507715967521516971883 101526761573951282275457825)
    ·
      refine ⟨76145071180463461706593369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101526761573951282275457825 76145071180463461706593369)
      ·
        refine ⟨57108803385347596279945027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76145071180463461706593369 57108803385347596279945027)
        ·
          refine ⟨85663205078021394419917541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57108803385347596279945027 85663205078021394419917541)
          ·
            refine ⟨16061850952129011453734539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85663205078021394419917541 16061850952129011453734539)
            ·
              refine ⟨24092776428193517180601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16061850952129011453734539 24092776428193517180601809)
              ·
                refine ⟨18069582321145137885451357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24092776428193517180601809 18069582321145137885451357)
                ·
                  refine ⟨6776093370429426707044259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18069582321145137885451357 6776093370429426707044259)
                  ·
                    refine ⟨10164140055644140060566389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776093370429426707044259 10164140055644140060566389)
                    ·
                      refine ⟨952888130216638130678099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10164140055644140060566389 952888130216638130678099)
                      ·
                        rfl

theorem cell23_1855743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_1855743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855743 prefixEnd_1855743 := by exact prefixLift 1855743
  have htrace : WordTrace (prefixWord ++ tailWord_1855743) baseStart_1855743 baseEnd_1855743 := by
    simpa [prefixWord, tailWord_1855743, baseEnd_1855743] using wordTrace_append hprefix tailTrace_1855743
  have hstable : (prefixWord ++ tailWord_1855743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855743).length < 2 ^ (prefixWord ++ tailWord_1855743).sum := by decide
  have hdescent : baseEnd_1855743 < baseStart_1855743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855780 : List Nat := [2, 3, 1, 3, 1, 3, 2, 8]
def baseStart_1855780 : Nat := 118140960795 + 1855780 * 2 ^ 59
def prefixEnd_1855780 : Nat := 4983230072969 + 3 ^ 40 * 1855780 * 2
def baseEnd_1855780 : Nat := 35292856629661277256127

theorem tailTrace_1855780 : CollatzResearch.WordTrace tailWord_1855780 prefixEnd_1855780 35292856629661277256127 := by
  unfold tailWord_1855780
  simp only [CollatzResearch.WordTrace]
  refine ⟨33842928608416738418034397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45123904811222317890712529 33842928608416738418034397)
  ·
    refine ⟨12691098228156276906762899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33842928608416738418034397 12691098228156276906762899)
    ·
      refine ⟨19036647342234415360144349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12691098228156276906762899 19036647342234415360144349)
      ·
        refine ⟨7138742753337905760054131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19036647342234415360144349 7138742753337905760054131)
        ·
          refine ⟨10708114130006858640081197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138742753337905760054131 10708114130006858640081197)
          ·
            refine ⟨4015542798752571990030449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10708114130006858640081197 4015542798752571990030449)
            ·
              refine ⟨3011657099064428992522837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015542798752571990030449 3011657099064428992522837)
              ·
                refine ⟨35292856629661277256127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3011657099064428992522837 35292856629661277256127)
                ·
                  rfl

theorem cell23_1855780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 8].length) (baseStart_1855780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855780 prefixEnd_1855780 := by exact prefixLift 1855780
  have htrace : WordTrace (prefixWord ++ tailWord_1855780) baseStart_1855780 baseEnd_1855780 := by
    simpa [prefixWord, tailWord_1855780, baseEnd_1855780] using wordTrace_append hprefix tailTrace_1855780
  have hstable : (prefixWord ++ tailWord_1855780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855780).length < 2 ^ (prefixWord ++ tailWord_1855780).sum := by decide
  have hdescent : baseEnd_1855780 < baseStart_1855780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855784 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1855784 : Nat := 118140960795 + 1855784 * 2 ^ 59
def prefixEnd_1855784 : Nat := 4983230072969 + 3 ^ 40 * 1855784 * 2
def baseEnd_1855784 : Nat := 317636394307824156755137

theorem tailTrace_1855784 : CollatzResearch.WordTrace tailWord_1855784 prefixEnd_1855784 317636394307824156755137 := by
  unfold tailWord_1855784
  simp only [CollatzResearch.WordTrace]
  refine ⟨33843001554409492759607203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45124002072545990346142937 33843001554409492759607203)
  ·
    refine ⟨50764502331614239139410805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33843001554409492759607203 50764502331614239139410805)
    ·
      refine ⟨4759172093588834919319763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50764502331614239139410805 4759172093588834919319763)
      ·
        refine ⟨7138758140383252378979645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759172093588834919319763 7138758140383252378979645)
        ·
          refine ⟨2677034302643719642117367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7138758140383252378979645 2677034302643719642117367)
          ·
            refine ⟨4015551453965579463176051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677034302643719642117367 4015551453965579463176051)
            ·
              refine ⟨6023327180948369194764077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015551453965579463176051 6023327180948369194764077)
              ·
                refine ⟨2258747692855638448036529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6023327180948369194764077 2258747692855638448036529)
                ·
                  refine ⟨1694060769641728836027397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2258747692855638448036529 1694060769641728836027397)
                  ·
                    refine ⟨317636394307824156755137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1694060769641728836027397 317636394307824156755137)
                    ·
                      rfl

theorem cell23_1855784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1855784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855784 prefixEnd_1855784 := by exact prefixLift 1855784
  have htrace : WordTrace (prefixWord ++ tailWord_1855784) baseStart_1855784 baseEnd_1855784 := by
    simpa [prefixWord, tailWord_1855784, baseEnd_1855784] using wordTrace_append hprefix tailTrace_1855784
  have hstable : (prefixWord ++ tailWord_1855784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855784).length < 2 ^ (prefixWord ++ tailWord_1855784).sum := by decide
  have hdescent : baseEnd_1855784 < baseStart_1855784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855824 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 2, 1, 3]
def baseStart_1855824 : Nat := 118140960795 + 1855824 * 2 ^ 59
def prefixEnd_1855824 : Nat := 4983230072969 + 3 ^ 40 * 1855824 * 2
def baseEnd_1855824 : Nat := 952929722149652313765227

theorem tailTrace_1855824 : CollatzResearch.WordTrace tailWord_1855824 prefixEnd_1855824 952929722149652313765227 := by
  unfold tailWord_1855824
  simp only [CollatzResearch.WordTrace]
  refine ⟨33843731014337036175335263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45124974685782714900447017 33843731014337036175335263)
  ·
    refine ⟨50765596521505554263002895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33843731014337036175335263 50765596521505554263002895)
    ·
      refine ⟨76148394782258331394504343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50765596521505554263002895 76148394782258331394504343)
      ·
        refine ⟨114222592173387497091756515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76148394782258331394504343 114222592173387497091756515)
        ·
          refine ⟨171333888260081245637634773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114222592173387497091756515 171333888260081245637634773)
          ·
            refine ⟨4015638006095654194632065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 171333888260081245637634773 4015638006095654194632065)
            ·
              refine ⟨3011728504571740645974049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015638006095654194632065 3011728504571740645974049)
              ·
                refine ⟨2258796378428805484480537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011728504571740645974049 2258796378428805484480537)
                ·
                  refine ⟨1694097283821604113360403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2258796378428805484480537 1694097283821604113360403)
                  ·
                    refine ⟨2541145925732406170040605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1694097283821604113360403 2541145925732406170040605)
                    ·
                      refine ⟨952929722149652313765227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2541145925732406170040605 952929722149652313765227)
                      ·
                        rfl

theorem cell23_1855824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 1, 3].length) (baseStart_1855824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855824 prefixEnd_1855824 := by exact prefixLift 1855824
  have htrace : WordTrace (prefixWord ++ tailWord_1855824) baseStart_1855824 baseEnd_1855824 := by
    simpa [prefixWord, tailWord_1855824, baseEnd_1855824] using wordTrace_append hprefix tailTrace_1855824
  have hstable : (prefixWord ++ tailWord_1855824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855824).length < 2 ^ (prefixWord ++ tailWord_1855824).sum := by decide
  have hdescent : baseEnd_1855824 < baseStart_1855824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855881 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 2, 2, 2]
def baseStart_1855881 : Nat := 118140960795 + 1855881 * 2 ^ 59
def prefixEnd_1855881 : Nat := 4983230072969 + 3 ^ 40 * 1855881 * 2
def baseEnd_1855881 : Nat := 952958990546958590752465

theorem tailTrace_1855881 : CollatzResearch.WordTrace tailWord_1855881 prefixEnd_1855881 952958990546958590752465 := by
  unfold tailWord_1855881
  simp only [CollatzResearch.WordTrace]
  refine ⟨67689540989467571085495497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45126360659645047390330331 67689540989467571085495497)
  ·
    refine ⟨50767155742100678314121623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67689540989467571085495497 50767155742100678314121623)
    ·
      refine ⟨76150733613151017471182435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50767155742100678314121623 76150733613151017471182435)
      ·
        refine ⟨114226100419726526206773653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76150733613151017471182435 114226100419726526206773653)
        ·
          refine ⟨5354348457174680915942515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114226100419726526206773653 5354348457174680915942515)
          ·
            refine ⟨8031522685762021373913773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354348457174680915942515 8031522685762021373913773)
            ·
              refine ⟨3011821007160758015217665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8031522685762021373913773 3011821007160758015217665)
              ·
                refine ⟨2258865755370568511413249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011821007160758015217665 2258865755370568511413249)
                ·
                  refine ⟨1694149316527926383559937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2258865755370568511413249 1694149316527926383559937)
                  ·
                    refine ⟨1270611987395944787669953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694149316527926383559937 1270611987395944787669953)
                    ·
                      refine ⟨952958990546958590752465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270611987395944787669953 952958990546958590752465)
                      ·
                        rfl

theorem cell23_1855881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 2, 2].length) (baseStart_1855881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855881 prefixEnd_1855881 := by exact prefixLift 1855881
  have htrace : WordTrace (prefixWord ++ tailWord_1855881) baseStart_1855881 baseEnd_1855881 := by
    simpa [prefixWord, tailWord_1855881, baseEnd_1855881] using wordTrace_append hprefix tailTrace_1855881
  have hstable : (prefixWord ++ tailWord_1855881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855881).length < 2 ^ (prefixWord ++ tailWord_1855881).sum := by decide
  have hdescent : baseEnd_1855881 < baseStart_1855881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855898 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2]
def baseStart_1855898 : Nat := 118140960795 + 1855898 * 2 ^ 59
def prefixEnd_1855898 : Nat := 4983230072969 + 3 ^ 40 * 1855898 * 2
def baseEnd_1855898 : Nat := 952967719718085024239887

theorem tailTrace_1855898 : CollatzResearch.WordTrace tailWord_1855898 prefixEnd_1855898 952967719718085024239887 := by
  unfold tailWord_1855898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922540257601495747216087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45126774020270655325909565 16922540257601495747216087)
  ·
    refine ⟨25383810386402243620824131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16922540257601495747216087 25383810386402243620824131)
    ·
      refine ⟨38075715579603365431236197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25383810386402243620824131 38075715579603365431236197)
      ·
        refine ⟨7139196671175631018356787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38075715579603365431236197 7139196671175631018356787)
        ·
          refine ⟨10708795006763446527535181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139196671175631018356787 10708795006763446527535181)
          ·
            refine ⟨4015798127536292447825693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10708795006763446527535181 4015798127536292447825693)
            ·
              refine ⟨1505924297826109667934635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4015798127536292447825693 1505924297826109667934635)
              ·
                refine ⟨2258886446739164501901953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505924297826109667934635 2258886446739164501901953)
                ·
                  refine ⟨1694164835054373376426465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2258886446739164501901953 1694164835054373376426465)
                  ·
                    refine ⟨1270623626290780032319849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694164835054373376426465 1270623626290780032319849)
                    ·
                      refine ⟨952967719718085024239887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270623626290780032319849 952967719718085024239887)
                      ·
                        rfl

theorem cell23_1855898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_1855898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1855898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1855898 prefixEnd_1855898 := by exact prefixLift 1855898
  have htrace : WordTrace (prefixWord ++ tailWord_1855898) baseStart_1855898 baseEnd_1855898 := by
    simpa [prefixWord, tailWord_1855898, baseEnd_1855898] using wordTrace_append hprefix tailTrace_1855898
  have hstable : (prefixWord ++ tailWord_1855898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855898).length < 2 ^ (prefixWord ++ tailWord_1855898).sum := by decide
  have hdescent : baseEnd_1855898 < baseStart_1855898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856000 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1856000 : Nat := 118140960795 + 1856000 * 2 ^ 59
def prefixEnd_1856000 : Nat := 4983230072969 + 3 ^ 40 * 1856000 * 2
def baseEnd_1856000 : Nat := 953020094744843625164417

theorem tailTrace_1856000 : CollatzResearch.WordTrace tailWord_1856000 prefixEnd_1856000 953020094744843625164417 := by
  unfold tailWord_1856000
  simp only [CollatzResearch.WordTrace]
  refine ⟨33846940638018227204538727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45129254184024302939384969 33846940638018227204538727)
  ·
    refine ⟨50770410957027340806808091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33846940638018227204538727 50770410957027340806808091)
    ·
      refine ⟨76155616435541011210212137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50770410957027340806808091 76155616435541011210212137)
      ·
        refine ⟨57116712326655758407659103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76155616435541011210212137 57116712326655758407659103)
        ·
          refine ⟨85675068489983637611488655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57116712326655758407659103 85675068489983637611488655)
          ·
            refine ⟨128512602734975456417232983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85675068489983637611488655 128512602734975456417232983)
            ·
              refine ⟨192768904102463184625849475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128512602734975456417232983 192768904102463184625849475)
              ·
                refine ⟨289153356153694776938774213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192768904102463184625849475 289153356153694776938774213)
                ·
                  refine ⟨54216254278817770676020165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289153356153694776938774213 54216254278817770676020165)
                  ·
                    refine ⟨10165547677278332001753781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54216254278817770676020165 10165547677278332001753781)
                    ·
                      refine ⟨953020094744843625164417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10165547677278332001753781 953020094744843625164417)
                      ·
                        rfl

theorem cell23_1856000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1856000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856000 prefixEnd_1856000 := by exact prefixLift 1856000
  have htrace : WordTrace (prefixWord ++ tailWord_1856000) baseStart_1856000 baseEnd_1856000 := by
    simpa [prefixWord, tailWord_1856000, baseEnd_1856000] using wordTrace_append hprefix tailTrace_1856000
  have hstable : (prefixWord ++ tailWord_1856000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856000).length < 2 ^ (prefixWord ++ tailWord_1856000).sum := by decide
  have hdescent : baseEnd_1856000 < baseStart_1856000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856037 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_1856037 : Nat := 118140960795 + 1856037 * 2 ^ 59
def prefixEnd_1856037 : Nat := 4983230072969 + 3 ^ 40 * 1856037 * 2
def baseEnd_1856037 : Nat := 317679697843019993467249

theorem tailTrace_1856037 : CollatzResearch.WordTrace tailWord_1856037 prefixEnd_1856037 317679697843019993467249 := by
  unfold tailWord_1856037
  simp only [CollatzResearch.WordTrace]
  refine ⟨67695230776902409728174365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45130153851268273152116243 67695230776902409728174365)
  ·
    refine ⟨25385711541338403648065387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67695230776902409728174365 25385711541338403648065387)
    ·
      refine ⟨38078567312007605472098081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25385711541338403648065387 38078567312007605472098081)
      ·
        refine ⟨28558925484005704104073561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38078567312007605472098081 28558925484005704104073561)
        ·
          refine ⟨21419194113004278078055171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28558925484005704104073561 21419194113004278078055171)
          ·
            refine ⟨32128791169506417117082757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21419194113004278078055171 32128791169506417117082757)
            ·
              refine ⟨6024148344282453209453017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32128791169506417117082757 6024148344282453209453017)
              ·
                refine ⟨4518111258211839907089763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6024148344282453209453017 4518111258211839907089763)
                ·
                  refine ⟨6777166887317759860634645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518111258211839907089763 6777166887317759860634645)
                  ·
                    refine ⟨317679697843019993467249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6777166887317759860634645 317679697843019993467249)
                    ·
                      rfl

theorem cell23_1856037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_1856037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856037 prefixEnd_1856037 := by exact prefixLift 1856037
  have htrace : WordTrace (prefixWord ++ tailWord_1856037) baseStart_1856037 baseEnd_1856037 := by
    simpa [prefixWord, tailWord_1856037, baseEnd_1856037] using wordTrace_append hprefix tailTrace_1856037
  have hstable : (prefixWord ++ tailWord_1856037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856037).length < 2 ^ (prefixWord ++ tailWord_1856037).sum := by decide
  have hdescent : baseEnd_1856037 < baseStart_1856037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856045 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1856045 : Nat := 118140960795 + 1856045 * 2 ^ 59
def prefixEnd_1856045 : Nat := 4983230072969 + 3 ^ 40 * 1856045 * 2
def baseEnd_1856045 : Nat := 105893689041588438789079

theorem tailTrace_1856045 : CollatzResearch.WordTrace tailWord_1856045 prefixEnd_1856045 105893689041588438789079 := by
  unfold tailWord_1856045
  simp only [CollatzResearch.WordTrace]
  refine ⟨67695522560873427094465589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45130348373915618062977059 67695522560873427094465589)
  ·
    refine ⟨6346455240081883790106149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67695522560873427094465589 6346455240081883790106149)
    ·
      refine ⟨1189960357515353210644903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6346455240081883790106149 1189960357515353210644903)
      ·
        refine ⟨1784940536273029815967355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189960357515353210644903 1784940536273029815967355)
        ·
          refine ⟨2677410804409544723951033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784940536273029815967355 2677410804409544723951033)
          ·
            refine ⟨2008058103307158542963275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677410804409544723951033 2008058103307158542963275)
            ·
              refine ⟨3012087154960737814444913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008058103307158542963275 3012087154960737814444913)
              ·
                refine ⟨2259065366220553360833685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012087154960737814444913 2259065366220553360833685)
                ·
                  refine ⟨105893689041588438789079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2259065366220553360833685 105893689041588438789079)
                  ·
                    rfl

theorem cell23_1856045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1856045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856045 prefixEnd_1856045 := by exact prefixLift 1856045
  have htrace : WordTrace (prefixWord ++ tailWord_1856045) baseStart_1856045 baseEnd_1856045 := by
    simpa [prefixWord, tailWord_1856045, baseEnd_1856045] using wordTrace_append hprefix tailTrace_1856045
  have hstable : (prefixWord ++ tailWord_1856045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856045).length < 2 ^ (prefixWord ++ tailWord_1856045).sum := by decide
  have hdescent : baseEnd_1856045 < baseStart_1856045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856057 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1856057 : Nat := 118140960795 + 1856057 * 2 ^ 59
def prefixEnd_1856057 : Nat := 4983230072969 + 3 ^ 40 * 1856057 * 2
def baseEnd_1856057 : Nat := 953049363142149902151655

theorem tailTrace_1856057 : CollatzResearch.WordTrace tailWord_1856057 prefixEnd_1856057 953049363142149902151655 := by
  unfold tailWord_1856057
  simp only [CollatzResearch.WordTrace]
  refine ⟨67695960236829953143902425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45130640157886635429268283 67695960236829953143902425)
  ·
    refine ⟨50771970177622464857926819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67695960236829953143902425 50771970177622464857926819)
    ·
      refine ⟨76157955266433697286890229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50771970177622464857926819 76157955266433697286890229)
      ·
        refine ⟨7139808306228159120645959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76157955266433697286890229 7139808306228159120645959)
        ·
          refine ⟨10709712459342238680968939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139808306228159120645959 10709712459342238680968939)
          ·
            refine ⟨16064568689013358021453409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709712459342238680968939 16064568689013358021453409)
            ·
              refine ⟨12048426516760018516090057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16064568689013358021453409 12048426516760018516090057)
              ·
                refine ⟨9036319887570013887067543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12048426516760018516090057 9036319887570013887067543)
                ·
                  refine ⟨13554479831355020830601315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9036319887570013887067543 13554479831355020830601315)
                  ·
                    refine ⟨20331719747032531245901973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13554479831355020830601315 20331719747032531245901973)
                    ·
                      refine ⟨953049363142149902151655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20331719747032531245901973 953049363142149902151655)
                      ·
                        rfl

theorem cell23_1856057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1856057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856057 prefixEnd_1856057 := by exact prefixLift 1856057
  have htrace : WordTrace (prefixWord ++ tailWord_1856057) baseStart_1856057 baseEnd_1856057 := by
    simpa [prefixWord, tailWord_1856057, baseEnd_1856057] using wordTrace_append hprefix tailTrace_1856057
  have hstable : (prefixWord ++ tailWord_1856057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856057).length < 2 ^ (prefixWord ++ tailWord_1856057).sum := by decide
  have hdescent : baseEnd_1856057 < baseStart_1856057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856074 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_1856074 : Nat := 118140960795 + 1856074 * 2 ^ 59
def prefixEnd_1856074 : Nat := 4983230072969 + 3 ^ 40 * 1856074 * 2
def baseEnd_1856074 : Nat := 953058092313276335639077

theorem tailTrace_1856074 : CollatzResearch.WordTrace tailWord_1856074 prefixEnd_1856074 953058092313276335639077 := by
  unfold tailWord_1856074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924145069442091261817819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45131053518512243364847517 16924145069442091261817819)
  ·
    refine ⟨25386217604163136892726729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16924145069442091261817819 25386217604163136892726729)
    ·
      refine ⟨19039663203122352669545047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25386217604163136892726729 19039663203122352669545047)
      ·
        refine ⟨28559494804683529004317571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19039663203122352669545047 28559494804683529004317571)
        ·
          refine ⟨42839242207025293506476357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28559494804683529004317571 42839242207025293506476357)
          ·
            refine ⟨8032357913817242532464317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42839242207025293506476357 8032357913817242532464317)
            ·
              refine ⟨3012134217681465949674119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8032357913817242532464317 3012134217681465949674119)
              ·
                refine ⟨4518201326522198924511179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012134217681465949674119 4518201326522198924511179)
                ·
                  refine ⟨6777301989783298386766769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518201326522198924511179 6777301989783298386766769)
                  ·
                    refine ⟨5082976492337473790075077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777301989783298386766769 5082976492337473790075077)
                    ·
                      refine ⟨953058092313276335639077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5082976492337473790075077 953058092313276335639077)
                      ·
                        rfl

theorem cell23_1856074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_1856074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856074 prefixEnd_1856074 := by exact prefixLift 1856074
  have htrace : WordTrace (prefixWord ++ tailWord_1856074) baseStart_1856074 baseEnd_1856074 := by
    simpa [prefixWord, tailWord_1856074, baseEnd_1856074] using wordTrace_append hprefix tailTrace_1856074
  have hstable : (prefixWord ++ tailWord_1856074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856074).length < 2 ^ (prefixWord ++ tailWord_1856074).sum := by decide
  have hdescent : baseEnd_1856074 < baseStart_1856074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856081 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 3]
def baseStart_1856081 : Nat := 118140960795 + 1856081 * 2 ^ 59
def prefixEnd_1856081 : Nat := 4983230072969 + 3 ^ 40 * 1856081 * 2
def baseEnd_1856081 : Nat := 953061686677857808251545

theorem tailTrace_1856081 : CollatzResearch.WordTrace tailWord_1856081 prefixEnd_1856081 953061686677857808251545 := by
  unfold tailWord_1856081
  simp only [CollatzResearch.WordTrace]
  refine ⟨67696835588743005242776097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45131223725828670161850731 67696835588743005242776097)
  ·
    refine ⟨50772626691557253932082073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67696835588743005242776097 50772626691557253932082073)
    ·
      refine ⟨38079470018667940449061555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50772626691557253932082073 38079470018667940449061555)
      ·
        refine ⟨57119205028001910673592333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38079470018667940449061555 57119205028001910673592333)
        ·
          refine ⟨21419701885500716502597125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57119205028001910673592333 21419701885500716502597125)
          ·
            refine ⟨4016194103531384344236961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21419701885500716502597125 4016194103531384344236961)
            ·
              refine ⟨3012145577648538258177721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4016194103531384344236961 3012145577648538258177721)
              ·
                refine ⟨2259109183236403693633291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012145577648538258177721 2259109183236403693633291)
                ·
                  refine ⟨3388663774854605540449937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259109183236403693633291 3388663774854605540449937)
                  ·
                    refine ⟨2541497831140954155337453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3388663774854605540449937 2541497831140954155337453)
                    ·
                      refine ⟨953061686677857808251545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2541497831140954155337453 953061686677857808251545)
                      ·
                        rfl

theorem cell23_1856081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_1856081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856081 prefixEnd_1856081 := by exact prefixLift 1856081
  have htrace : WordTrace (prefixWord ++ tailWord_1856081) baseStart_1856081 baseEnd_1856081 := by
    simpa [prefixWord, tailWord_1856081, baseEnd_1856081] using wordTrace_append hprefix tailTrace_1856081
  have hstable : (prefixWord ++ tailWord_1856081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856081).length < 2 ^ (prefixWord ++ tailWord_1856081).sum := by decide
  have hdescent : baseEnd_1856081 < baseStart_1856081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856084 : List Nat := [2, 4, 1, 1, 1, 3, 4, 7]
def baseStart_1856084 : Nat := 118140960795 + 1856084 * 2 ^ 59
def prefixEnd_1856084 : Nat := 4983230072969 + 3 ^ 40 * 1856084 * 2
def baseEnd_1856084 : Nat := 35298638041474862833853

theorem tailTrace_1856084 : CollatzResearch.WordTrace tailWord_1856084 prefixEnd_1856084 35298638041474862833853 := by
  unfold tailWord_1856084
  simp only [CollatzResearch.WordTrace]
  refine ⟨33848472503866068377567653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45131296671821424503423537 33848472503866068377567653)
  ·
    refine ⟨6346588594474887820793935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33848472503866068377567653 6346588594474887820793935)
    ·
      refine ⟨9519882891712331731190903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6346588594474887820793935 9519882891712331731190903)
      ·
        refine ⟨14279824337568497596786355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9519882891712331731190903 14279824337568497596786355)
        ·
          refine ⟨21419736506352746395179533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14279824337568497596786355 21419736506352746395179533)
          ·
            refine ⟨8032401189882279898192325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21419736506352746395179533 8032401189882279898192325)
            ·
              refine ⟨1506075223102927480911061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8032401189882279898192325 1506075223102927480911061)
              ·
                refine ⟨35298638041474862833853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1506075223102927480911061 35298638041474862833853)
                ·
                  rfl

theorem cell23_1856084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 7].length) (baseStart_1856084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856084 prefixEnd_1856084 := by exact prefixLift 1856084
  have htrace : WordTrace (prefixWord ++ tailWord_1856084) baseStart_1856084 baseEnd_1856084 := by
    simpa [prefixWord, tailWord_1856084, baseEnd_1856084] using wordTrace_append hprefix tailTrace_1856084
  have hstable : (prefixWord ++ tailWord_1856084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856084).length < 2 ^ (prefixWord ++ tailWord_1856084).sum := by decide
  have hdescent : baseEnd_1856084 < baseStart_1856084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856098 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1856098 : Nat := 118140960795 + 1856098 * 2 ^ 59
def prefixEnd_1856098 : Nat := 4983230072969 + 3 ^ 40 * 1856098 * 2
def baseEnd_1856098 : Nat := 953070415848984241738967

theorem tailTrace_1856098 : CollatzResearch.WordTrace tailWord_1856098 prefixEnd_1856098 953070415848984241738967 := by
  unfold tailWord_1856098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924363907420354286536237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45131637086454278097429965 16924363907420354286536237)
  ·
    refine ⟨6346636465282632857451089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16924363907420354286536237 6346636465282632857451089)
    ·
      refine ⟨4759977348961974643088317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6346636465282632857451089 4759977348961974643088317)
      ·
        refine ⟨1784991505860740491158119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4759977348961974643088317 1784991505860740491158119)
        ·
          refine ⟨2677487258791110736737179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784991505860740491158119 2677487258791110736737179)
          ·
            refine ⟨4016230888186666105105769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677487258791110736737179 4016230888186666105105769)
            ·
              refine ⟨3012173166139999578829327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4016230888186666105105769 3012173166139999578829327)
              ·
                refine ⟨4518259749209999368243991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012173166139999578829327 4518259749209999368243991)
                ·
                  refine ⟨6777389623814999052365987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518259749209999368243991 6777389623814999052365987)
                  ·
                    refine ⟨10166084435722498578548981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6777389623814999052365987 10166084435722498578548981)
                    ·
                      refine ⟨953070415848984241738967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10166084435722498578548981 953070415848984241738967)
                      ·
                        rfl

theorem cell23_1856098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1856098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856098 prefixEnd_1856098 := by exact prefixLift 1856098
  have htrace : WordTrace (prefixWord ++ tailWord_1856098) baseStart_1856098 baseEnd_1856098 := by
    simpa [prefixWord, tailWord_1856098, baseEnd_1856098] using wordTrace_append hprefix tailTrace_1856098
  have hstable : (prefixWord ++ tailWord_1856098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856098).length < 2 ^ (prefixWord ++ tailWord_1856098).sum := by decide
  have hdescent : baseEnd_1856098 < baseStart_1856098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856112 : List Nat := [2, 1, 1, 1, 7, 1, 3, 2, 1, 2, 2]
def baseStart_1856112 : Nat := 118140960795 + 1856112 * 2 ^ 59
def prefixEnd_1856112 : Nat := 4983230072969 + 3 ^ 40 * 1856112 * 2
def baseEnd_1856112 : Nat := 953077604578147186963903

theorem tailTrace_1856112 : CollatzResearch.WordTrace tailWord_1856112 prefixEnd_1856112 953077604578147186963903 := by
  unfold tailWord_1856112
  simp only [CollatzResearch.WordTrace]
  refine ⟨33848983125815348768577295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45131977501087131691436393 33848983125815348768577295)
  ·
    refine ⟨50773474688723023152865943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33848983125815348768577295 50773474688723023152865943)
    ·
      refine ⟨76160212033084534729298915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50773474688723023152865943 76160212033084534729298915)
      ·
        refine ⟨114240318049626802093948373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76160212033084534729298915 114240318049626802093948373)
        ·
          refine ⟨2677507454288128174076915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 114240318049626802093948373 2677507454288128174076915)
          ·
            refine ⟨4016261181432192261115373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677507454288128174076915 4016261181432192261115373)
            ·
              refine ⟨1506097943037072097918265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4016261181432192261115373 1506097943037072097918265)
              ·
                refine ⟨1129573457277804073438699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506097943037072097918265 1129573457277804073438699)
                ·
                  refine ⟨1694360185916706110158049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129573457277804073438699 1694360185916706110158049)
                  ·
                    refine ⟨1270770139437529582618537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694360185916706110158049 1270770139437529582618537)
                    ·
                      refine ⟨953077604578147186963903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270770139437529582618537 953077604578147186963903)
                      ·
                        rfl

theorem cell23_1856112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 2, 2].length) (baseStart_1856112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856112 prefixEnd_1856112 := by exact prefixLift 1856112
  have htrace : WordTrace (prefixWord ++ tailWord_1856112) baseStart_1856112 baseEnd_1856112 := by
    simpa [prefixWord, tailWord_1856112, baseEnd_1856112] using wordTrace_append hprefix tailTrace_1856112
  have hstable : (prefixWord ++ tailWord_1856112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856112).length < 2 ^ (prefixWord ++ tailWord_1856112).sum := by decide
  have hdescent : baseEnd_1856112 < baseStart_1856112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856128 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 2, 1, 3]
def baseStart_1856128 : Nat := 118140960795 + 1856128 * 2 ^ 59
def prefixEnd_1856128 : Nat := 4983230072969 + 3 ^ 40 * 1856128 * 2
def baseEnd_1856128 : Nat := 953085820268619124363829

theorem tailTrace_1856128 : CollatzResearch.WordTrace tailWord_1856128 prefixEnd_1856128 953085820268619124363829 := by
  unfold tailWord_1856128
  simp only [CollatzResearch.WordTrace]
  refine ⟨33849274909786366134868519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45132366546381821513158025 33849274909786366134868519)
  ·
    refine ⟨50773912364679549202302779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33849274909786366134868519 50773912364679549202302779)
    ·
      refine ⟨76160868547019323803454169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50773912364679549202302779 76160868547019323803454169)
      ·
        refine ⟨57120651410264492852590627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76160868547019323803454169 57120651410264492852590627)
        ·
          refine ⟨85680977115396739278885941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57120651410264492852590627 85680977115396739278885941)
          ·
            refine ⟨8032591604568444307395557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85680977115396739278885941 8032591604568444307395557)
            ·
              refine ⟨1506110925856583307636667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8032591604568444307395557 1506110925856583307636667)
              ·
                refine ⟨2259166388784874961455001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506110925856583307636667 2259166388784874961455001)
                ·
                  refine ⟨1694374791588656221091251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259166388784874961455001 1694374791588656221091251)
                  ·
                    refine ⟨2541562187382984331636877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1694374791588656221091251 2541562187382984331636877)
                    ·
                      refine ⟨953085820268619124363829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2541562187382984331636877 953085820268619124363829)
                      ·
                        rfl

theorem cell23_1856128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_1856128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856128 prefixEnd_1856128 := by exact prefixLift 1856128
  have htrace : WordTrace (prefixWord ++ tailWord_1856128) baseStart_1856128 baseEnd_1856128 := by
    simpa [prefixWord, tailWord_1856128, baseEnd_1856128] using wordTrace_append hprefix tailTrace_1856128
  have hstable : (prefixWord ++ tailWord_1856128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856128).length < 2 ^ (prefixWord ++ tailWord_1856128).sum := by decide
  have hdescent : baseEnd_1856128 < baseStart_1856128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856138 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_1856138 : Nat := 118140960795 + 1856138 * 2 ^ 59
def prefixEnd_1856138 : Nat := 4983230072969 + 3 ^ 40 * 1856138 * 2
def baseEnd_1856138 : Nat := 953090955075164085238783

theorem tailTrace_1856138 : CollatzResearch.WordTrace tailWord_1856138 prefixEnd_1856138 953090955075164085238783 := by
  unfold tailWord_1856138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924728637384125994400267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45132609699691002651734045 16924728637384125994400267)
  ·
    refine ⟨25387092956076188991600401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16924728637384125994400267 25387092956076188991600401)
    ·
      refine ⟨19040319717057141743700301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25387092956076188991600401 19040319717057141743700301)
      ·
        refine ⟨7140119893896428153887613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19040319717057141743700301 7140119893896428153887613)
        ·
          refine ⟨2677544960211160557707855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7140119893896428153887613 2677544960211160557707855)
          ·
            refine ⟨4016317440316740836561783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677544960211160557707855 4016317440316740836561783)
            ·
              refine ⟨6024476160475111254842675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016317440316740836561783 6024476160475111254842675)
              ·
                refine ⟨9036714240712666882264013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024476160475111254842675 9036714240712666882264013)
                ·
                  refine ⟨3388767840267250080849005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9036714240712666882264013 3388767840267250080849005)
                  ·
                    refine ⟨1270787940100218780318377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3388767840267250080849005 1270787940100218780318377)
                    ·
                      refine ⟨953090955075164085238783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270787940100218780318377 953090955075164085238783)
                      ·
                        rfl

theorem cell23_1856138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_1856138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856138 prefixEnd_1856138 := by exact prefixLift 1856138
  have htrace : WordTrace (prefixWord ++ tailWord_1856138) baseStart_1856138 baseEnd_1856138 := by
    simpa [prefixWord, tailWord_1856138, baseEnd_1856138] using wordTrace_append hprefix tailTrace_1856138
  have hstable : (prefixWord ++ tailWord_1856138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856138).length < 2 ^ (prefixWord ++ tailWord_1856138).sum := by decide
  have hdescent : baseEnd_1856138 < baseStart_1856138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856147 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4]
def baseStart_1856147 : Nat := 118140960795 + 1856147 * 2 ^ 59
def prefixEnd_1856147 : Nat := 4983230072969 + 3 ^ 40 * 1856147 * 2
def baseEnd_1856147 : Nat := 953095576401054550026241

theorem tailTrace_1856147 : CollatzResearch.WordTrace tailWord_1856147 prefixEnd_1856147 953095576401054550026241 := by
  unfold tailWord_1856147
  simp only [CollatzResearch.WordTrace]
  refine ⟨67699242806503898514678695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45132828537669265676452463 67699242806503898514678695)
  ·
    refine ⟨101548864209755847772018043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67699242806503898514678695 101548864209755847772018043)
    ·
      refine ⟨152323296314633771658027065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101548864209755847772018043 152323296314633771658027065)
      ·
        refine ⟨114242472235975328743520299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152323296314633771658027065 114242472235975328743520299)
        ·
          refine ⟨171363708353962993115280449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114242472235975328743520299 171363708353962993115280449)
          ·
            refine ⟨128522781265472244836460337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171363708353962993115280449 128522781265472244836460337)
            ·
              refine ⟨96392085949104183627345253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128522781265472244836460337 96392085949104183627345253)
              ·
                refine ⟨18073516115457034430127235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96392085949104183627345253 18073516115457034430127235)
                ·
                  refine ⟨27110274173185551645190853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18073516115457034430127235 27110274173185551645190853)
                  ·
                    refine ⟨5083176407472290933473285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27110274173185551645190853 5083176407472290933473285)
                    ·
                      refine ⟨953095576401054550026241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5083176407472290933473285 953095576401054550026241)
                      ·
                        rfl

theorem cell23_1856147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_1856147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856147 prefixEnd_1856147 := by exact prefixLift 1856147
  have htrace : WordTrace (prefixWord ++ tailWord_1856147) baseStart_1856147 baseEnd_1856147 := by
    simpa [prefixWord, tailWord_1856147, baseEnd_1856147] using wordTrace_append hprefix tailTrace_1856147
  have hstable : (prefixWord ++ tailWord_1856147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856147).length < 2 ^ (prefixWord ++ tailWord_1856147).sum := by decide
  have hdescent : baseEnd_1856147 < baseStart_1856147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856151 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 1, 4, 2]
def baseStart_1856151 : Nat := 118140960795 + 1856151 * 2 ^ 59
def prefixEnd_1856151 : Nat := 4983230072969 + 3 ^ 40 * 1856151 * 2
def baseEnd_1856151 : Nat := 953097630323672534376223

theorem tailTrace_1856151 : CollatzResearch.WordTrace tailWord_1856151 prefixEnd_1856151 953097630323672534376223 := by
  unfold tailWord_1856151
  simp only [CollatzResearch.WordTrace]
  refine ⟨67699388698489407197824307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45132925798992938131882871 67699388698489407197824307)
  ·
    refine ⟨101549083047734110796736461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67699388698489407197824307 101549083047734110796736461)
    ·
      refine ⟨38080906142900291548776173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101549083047734110796736461 38080906142900291548776173)
      ·
        refine ⟨14280339803587609330791065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38080906142900291548776173 14280339803587609330791065)
        ·
          refine ⟨10710254852690706998093299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14280339803587609330791065 10710254852690706998093299)
          ·
            refine ⟨16065382279036060497139949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10710254852690706998093299 16065382279036060497139949)
            ·
              refine ⟨6024518354638522686427481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16065382279036060497139949 6024518354638522686427481)
              ·
                refine ⟨4518388765978892014820611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6024518354638522686427481 4518388765978892014820611)
                ·
                  refine ⟨6777583148968338022230917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518388765978892014820611 6777583148968338022230917)
                  ·
                    refine ⟨1270796840431563379168297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6777583148968338022230917 1270796840431563379168297)
                    ·
                      refine ⟨953097630323672534376223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270796840431563379168297 953097630323672534376223)
                      ·
                        rfl

theorem cell23_1856151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_1856151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856151 prefixEnd_1856151 := by exact prefixLift 1856151
  have htrace : WordTrace (prefixWord ++ tailWord_1856151) baseStart_1856151 baseEnd_1856151 := by
    simpa [prefixWord, tailWord_1856151, baseEnd_1856151] using wordTrace_append hprefix tailTrace_1856151
  have hstable : (prefixWord ++ tailWord_1856151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856151).length < 2 ^ (prefixWord ++ tailWord_1856151).sum := by decide
  have hdescent : baseEnd_1856151 < baseStart_1856151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856164 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1856164 : Nat := 118140960795 + 1856164 * 2 ^ 59
def prefixEnd_1856164 : Nat := 4983230072969 + 3 ^ 40 * 1856164 * 2
def baseEnd_1856164 : Nat := 953104305572180983513663

theorem tailTrace_1856164 : CollatzResearch.WordTrace tailWord_1856164 prefixEnd_1856164 953104305572180983513663 := by
  unfold tailWord_1856164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33849931423721155209023773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45133241898294873612031697 33849931423721155209023773)
  ·
    refine ⟨12693724283895433203383915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33849931423721155209023773 12693724283895433203383915)
    ·
      refine ⟨19040586425843149805075873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12693724283895433203383915 19040586425843149805075873)
      ·
        refine ⟨14280439819382362353806905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19040586425843149805075873 14280439819382362353806905)
        ·
          refine ⟨10710329864536771765355179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14280439819382362353806905 10710329864536771765355179)
          ·
            refine ⟨16065494796805157648032769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10710329864536771765355179 16065494796805157648032769)
            ·
              refine ⟨12049121097603868236024577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16065494796805157648032769 12049121097603868236024577)
              ·
                refine ⟨9036840823202901177018433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12049121097603868236024577 9036840823202901177018433)
                ·
                  refine ⟨6777630617402175882763825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9036840823202901177018433 6777630617402175882763825)
                  ·
                    refine ⟨5083222963051631912072869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777630617402175882763825 5083222963051631912072869)
                    ·
                      refine ⟨953104305572180983513663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5083222963051631912072869 953104305572180983513663)
                      ·
                        rfl

theorem cell23_1856164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1856164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856164 prefixEnd_1856164 := by exact prefixLift 1856164
  have htrace : WordTrace (prefixWord ++ tailWord_1856164) baseStart_1856164 baseEnd_1856164 := by
    simpa [prefixWord, tailWord_1856164, baseEnd_1856164] using wordTrace_append hprefix tailTrace_1856164
  have hstable : (prefixWord ++ tailWord_1856164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856164).length < 2 ^ (prefixWord ++ tailWord_1856164).sum := by decide
  have hdescent : baseEnd_1856164 < baseStart_1856164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856181 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1856181 : Nat := 118140960795 + 1856181 * 2 ^ 59
def prefixEnd_1856181 : Nat := 4983230072969 + 3 ^ 40 * 1856181 * 2
def baseEnd_1856181 : Nat := 953113034743307417001085

theorem tailTrace_1856181 : CollatzResearch.WordTrace tailWord_1856181 prefixEnd_1856181 953113034743307417001085 := by
  unfold tailWord_1856181
  simp only [CollatzResearch.WordTrace]
  refine ⟨67700482888380722321416397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45133655258920481547610931 67700482888380722321416397)
  ·
    refine ⟨25387681083142770870531149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67700482888380722321416397 25387681083142770870531149)
    ·
      refine ⟨9520380406178539076449181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25387681083142770870531149 9520380406178539076449181)
      ·
        refine ⟨3570142652316952153668443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9520380406178539076449181 3570142652316952153668443)
        ·
          refine ⟨5355213978475428230502665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570142652316952153668443 5355213978475428230502665)
          ·
            refine ⟨4016410483856571172876999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5355213978475428230502665 4016410483856571172876999)
            ·
              refine ⟨6024615725784856759315499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016410483856571172876999 6024615725784856759315499)
              ·
                refine ⟨9036923588677285138973249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024615725784856759315499 9036923588677285138973249)
                ·
                  refine ⟨6777692691507963854229937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9036923588677285138973249 6777692691507963854229937)
                  ·
                    refine ⟨5083269518630972890672453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777692691507963854229937 5083269518630972890672453)
                    ·
                      refine ⟨953113034743307417001085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5083269518630972890672453 953113034743307417001085)
                      ·
                        rfl

theorem cell23_1856181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1856181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856181 prefixEnd_1856181 := by exact prefixLift 1856181
  have htrace : WordTrace (prefixWord ++ tailWord_1856181) baseStart_1856181 baseEnd_1856181 := by
    simpa [prefixWord, tailWord_1856181, baseEnd_1856181] using wordTrace_append hprefix tailTrace_1856181
  have hstable : (prefixWord ++ tailWord_1856181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856181).length < 2 ^ (prefixWord ++ tailWord_1856181).sum := by decide
  have hdescent : baseEnd_1856181 < baseStart_1856181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856224 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1856224 : Nat := 118140960795 + 1856224 * 2 ^ 59
def prefixEnd_1856224 : Nat := 4983230072969 + 3 ^ 40 * 1856224 * 2
def baseEnd_1856224 : Nat := 953135114411450748763387

theorem tailTrace_1856224 : CollatzResearch.WordTrace tailWord_1856224 prefixEnd_1856224 953135114411450748763387 := by
  unfold tailWord_1856224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33851025613612470332615863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45134700818149960443487817 33851025613612470332615863)
  ·
    refine ⟨50776538420418705498923795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33851025613612470332615863 50776538420418705498923795)
    ·
      refine ⟨76164807630628058248385693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50776538420418705498923795 76164807630628058248385693)
      ·
        refine ⟨28561802861485521843144635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76164807630628058248385693 28561802861485521843144635)
        ·
          refine ⟨42842704292228282764716953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28561802861485521843144635 42842704292228282764716953)
          ·
            refine ⟨32132028219171212073537715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42842704292228282764716953 32132028219171212073537715)
            ·
              refine ⟨48198042328756818110306573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32132028219171212073537715 48198042328756818110306573)
              ·
                refine ⟨18074265873283806791364965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48198042328756818110306573 18074265873283806791364965)
                ·
                  refine ⟨3388924851240713773380931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18074265873283806791364965 3388924851240713773380931)
                  ·
                    refine ⟨5083387276861070660071397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3388924851240713773380931 5083387276861070660071397)
                    ·
                      refine ⟨953135114411450748763387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5083387276861070660071397 953135114411450748763387)
                      ·
                        rfl

theorem cell23_1856224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1856224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856224 prefixEnd_1856224 := by exact prefixLift 1856224
  have htrace : WordTrace (prefixWord ++ tailWord_1856224) baseStart_1856224 baseEnd_1856224 := by
    simpa [prefixWord, tailWord_1856224, baseEnd_1856224] using wordTrace_append hprefix tailTrace_1856224
  have hstable : (prefixWord ++ tailWord_1856224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856224).length < 2 ^ (prefixWord ++ tailWord_1856224).sum := by decide
  have hdescent : baseEnd_1856224 < baseStart_1856224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856241 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 2, 4, 2]
def baseStart_1856241 : Nat := 118140960795 + 1856241 * 2 ^ 59
def prefixEnd_1856241 : Nat := 4983230072969 + 3 ^ 40 * 1856241 * 2
def baseEnd_1856241 : Nat := 953143843582577182250809

theorem tailTrace_1856241 : CollatzResearch.WordTrace tailWord_1856241 prefixEnd_1856241 953143843582577182250809 := by
  unfold tailWord_1856241
  simp only [CollatzResearch.WordTrace]
  refine ⟨67702671268163352568600577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45135114178775568379067051 67702671268163352568600577)
  ·
    refine ⟨50777003451122514426450433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67702671268163352568600577 50777003451122514426450433)
    ·
      refine ⟨38082752588341885819837825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50777003451122514426450433 38082752588341885819837825)
      ·
        refine ⟨28562064441256414364878369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38082752588341885819837825 28562064441256414364878369)
        ·
          refine ⟨21421548330942310773658777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28562064441256414364878369 21421548330942310773658777)
          ·
            refine ⟨16066161248206733080244083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21421548330942310773658777 16066161248206733080244083)
            ·
              refine ⟨24099241872310099620366125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16066161248206733080244083 24099241872310099620366125)
              ·
                refine ⟨9037215702116287357637297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24099241872310099620366125 9037215702116287357637297)
                ·
                  refine ⟨6777911776587215518227973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9037215702116287357637297 6777911776587215518227973)
                  ·
                    refine ⟨1270858458110102909667745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6777911776587215518227973 1270858458110102909667745)
                    ·
                      refine ⟨953143843582577182250809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270858458110102909667745 953143843582577182250809)
                      ·
                        rfl

theorem cell23_1856241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_1856241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856241 prefixEnd_1856241 := by exact prefixLift 1856241
  have htrace : WordTrace (prefixWord ++ tailWord_1856241) baseStart_1856241 baseEnd_1856241 := by
    simpa [prefixWord, tailWord_1856241, baseEnd_1856241] using wordTrace_append hprefix tailTrace_1856241
  have hstable : (prefixWord ++ tailWord_1856241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856241).length < 2 ^ (prefixWord ++ tailWord_1856241).sum := by decide
  have hdescent : baseEnd_1856241 < baseStart_1856241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856264 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 8]
def baseStart_1856264 : Nat := 118140960795 + 1856264 * 2 ^ 59
def prefixEnd_1856264 : Nat := 4983230072969 + 3 ^ 40 * 1856264 * 2
def baseEnd_1856264 : Nat := 105906183737514510251467

theorem tailTrace_1856264 : CollatzResearch.WordTrace tailWord_1856264 prefixEnd_1856264 105906183737514510251467 := by
  unfold tailWord_1856264
  simp only [CollatzResearch.WordTrace]
  refine ⟨33851755073540013748343923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45135673431386684997791897 33851755073540013748343923)
  ·
    refine ⟨50777632610310020622515885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33851755073540013748343923 50777632610310020622515885)
    ·
      refine ⟨19041612228866257733443457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50777632610310020622515885 19041612228866257733443457)
      ·
        refine ⟨14281209171649693300082593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19041612228866257733443457 14281209171649693300082593)
        ·
          refine ⟨10710906878737269975061945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14281209171649693300082593 10710906878737269975061945)
          ·
            refine ⟨8033180159052952481296459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10710906878737269975061945 8033180159052952481296459)
            ·
              refine ⟨12049770238579428721944689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8033180159052952481296459 12049770238579428721944689)
              ·
                refine ⟨9037327678934571541458517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12049770238579428721944689 9037327678934571541458517)
                ·
                  refine ⟨105906183737514510251467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9037327678934571541458517 105906183737514510251467)
                  ·
                    rfl

theorem cell23_1856264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 8].length) (baseStart_1856264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856264 prefixEnd_1856264 := by exact prefixLift 1856264
  have htrace : WordTrace (prefixWord ++ tailWord_1856264) baseStart_1856264 baseEnd_1856264 := by
    simpa [prefixWord, tailWord_1856264, baseEnd_1856264] using wordTrace_append hprefix tailTrace_1856264
  have hstable : (prefixWord ++ tailWord_1856264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856264).length < 2 ^ (prefixWord ++ tailWord_1856264).sum := by decide
  have hdescent : baseEnd_1856264 < baseStart_1856264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856328 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 1, 5]
def baseStart_1856328 : Nat := 118140960795 + 1856328 * 2 ^ 59
def prefixEnd_1856328 : Nat := 4983230072969 + 3 ^ 40 * 1856328 * 2
def baseEnd_1856328 : Nat := 317729505466506113954303

theorem tailTrace_1856328 : CollatzResearch.WordTrace tailWord_1856328 prefixEnd_1856328 317729505466506113954303 := by
  unfold tailWord_1856328
  simp only [CollatzResearch.WordTrace]
  refine ⟨33852922209424083213508819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45137229612565444284678425 33852922209424083213508819)
  ·
    refine ⟨50779383314136124820263229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33852922209424083213508819 50779383314136124820263229)
    ·
      refine ⟨19042268742801046807598711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50779383314136124820263229 19042268742801046807598711)
      ·
        refine ⟨28563403114201570211398067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19042268742801046807598711 28563403114201570211398067)
        ·
          refine ⟨42845104671302355317097101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28563403114201570211398067 42845104671302355317097101)
          ·
            refine ⟨16066914251738383243911413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42845104671302355317097101 16066914251738383243911413)
            ·
              refine ⟨1506273211100473429116695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16066914251738383243911413 1506273211100473429116695)
              ·
                refine ⟨2259409816650710143675043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506273211100473429116695 2259409816650710143675043)
                ·
                  refine ⟨3389114724976065215512565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259409816650710143675043 3389114724976065215512565)
                  ·
                    refine ⟨317729505466506113954303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3389114724976065215512565 317729505466506113954303)
                    ·
                      rfl

theorem cell23_1856328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_1856328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856328 prefixEnd_1856328 := by exact prefixLift 1856328
  have htrace : WordTrace (prefixWord ++ tailWord_1856328) baseStart_1856328 baseEnd_1856328 := by
    simpa [prefixWord, tailWord_1856328, baseEnd_1856328] using wordTrace_append hprefix tailTrace_1856328
  have hstable : (prefixWord ++ tailWord_1856328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856328).length < 2 ^ (prefixWord ++ tailWord_1856328).sum := by decide
  have hdescent : baseEnd_1856328 < baseStart_1856328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856344 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1856344 : Nat := 118140960795 + 1856344 * 2 ^ 59
def prefixEnd_1856344 : Nat := 4983230072969 + 3 ^ 40 * 1856344 * 2
def baseEnd_1856344 : Nat := 953196732089990279262835

theorem tailTrace_1856344 : CollatzResearch.WordTrace tailWord_1856344 prefixEnd_1856344 953196732089990279262835 := by
  unfold tailWord_1856344
  simp only [CollatzResearch.WordTrace]
  refine ⟨33853213993395100579800043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45137618657860134106400057 33853213993395100579800043)
  ·
    refine ⟨50779820990092650869700065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33853213993395100579800043 50779820990092650869700065)
    ·
      refine ⟨38084865742569488152275049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50779820990092650869700065 38084865742569488152275049)
      ·
        refine ⟨28563649306927116114206287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38084865742569488152275049 28563649306927116114206287)
        ·
          refine ⟨42845473960390674171309431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28563649306927116114206287 42845473960390674171309431)
          ·
            refine ⟨64268210940586011256964147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42845473960390674171309431 64268210940586011256964147)
            ·
              refine ⟨96402316410879016885446221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64268210940586011256964147 96402316410879016885446221)
              ·
                refine ⟨36150868654079631332042333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96402316410879016885446221 36150868654079631332042333)
                ·
                  refine ⟨13556575745279861749515875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36150868654079631332042333 13556575745279861749515875)
                  ·
                    refine ⟨20334863617919792624273813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13556575745279861749515875 20334863617919792624273813)
                    ·
                      refine ⟨953196732089990279262835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20334863617919792624273813 953196732089990279262835)
                      ·
                        rfl

theorem cell23_1856344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1856344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856344 prefixEnd_1856344 := by exact prefixLift 1856344
  have htrace : WordTrace (prefixWord ++ tailWord_1856344) baseStart_1856344 baseEnd_1856344 := by
    simpa [prefixWord, tailWord_1856344, baseEnd_1856344] using wordTrace_append hprefix tailTrace_1856344
  have hstable : (prefixWord ++ tailWord_1856344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856344).length < 2 ^ (prefixWord ++ tailWord_1856344).sum := by decide
  have hdescent : baseEnd_1856344 < baseStart_1856344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856348 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1856348 : Nat := 118140960795 + 1856348 * 2 ^ 59
def prefixEnd_1856348 : Nat := 4983230072969 + 3 ^ 40 * 1856348 * 2
def baseEnd_1856348 : Nat := 953198786012608263612817

theorem tailTrace_1856348 : CollatzResearch.WordTrace tailWord_1856348 prefixEnd_1856348 953198786012608263612817 := by
  unfold tailWord_1856348
  simp only [CollatzResearch.WordTrace]
  refine ⟨33853286939387854921372849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45137715919183806561830465 33853286939387854921372849)
  ·
    refine ⟨25389965204540891191029637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33853286939387854921372849 25389965204540891191029637)
    ·
      refine ⟨4760618475851417098318057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25389965204540891191029637 4760618475851417098318057)
      ·
        refine ⟨3570463856888562823738543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4760618475851417098318057 3570463856888562823738543)
        ·
          refine ⟨5355695785332844235607815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570463856888562823738543 5355695785332844235607815)
          ·
            refine ⟨8033543677999266353411723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355695785332844235607815 8033543677999266353411723)
            ·
              refine ⟨12050315516998899530117585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8033543677999266353411723 12050315516998899530117585)
              ·
                refine ⟨9037736637749174647588189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12050315516998899530117585 9037736637749174647588189)
                ·
                  refine ⟨3389151239155940492845571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9037736637749174647588189 3389151239155940492845571)
                  ·
                    refine ⟨5083726858733910739268357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389151239155940492845571 5083726858733910739268357)
                    ·
                      refine ⟨953198786012608263612817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5083726858733910739268357 953198786012608263612817)
                      ·
                        rfl

theorem cell23_1856348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1856348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856348 prefixEnd_1856348 := by exact prefixLift 1856348
  have htrace : WordTrace (prefixWord ++ tailWord_1856348) baseStart_1856348 baseEnd_1856348 := by
    simpa [prefixWord, tailWord_1856348, baseEnd_1856348] using wordTrace_append hprefix tailTrace_1856348
  have hstable : (prefixWord ++ tailWord_1856348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856348).length < 2 ^ (prefixWord ++ tailWord_1856348).sum := by decide
  have hdescent : baseEnd_1856348 < baseStart_1856348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856351 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 3]
def baseStart_1856351 : Nat := 118140960795 + 1856351 * 2 ^ 59
def prefixEnd_1856351 : Nat := 4983230072969 + 3 ^ 40 * 1856351 * 2
def baseEnd_1856351 : Nat := 953200326454571751875303

theorem tailTrace_1856351 : CollatzResearch.WordTrace tailWord_1856351 prefixEnd_1856351 953200326454571751875303 := by
  unfold tailWord_1856351
  simp only [CollatzResearch.WordTrace]
  refine ⟨67706683297764841355104907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45137788865176560903403271 67706683297764841355104907)
  ·
    refine ⟨101560024946647262032657361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67706683297764841355104907 101560024946647262032657361)
    ·
      refine ⟨76170018709985446524493021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101560024946647262032657361 76170018709985446524493021)
      ·
        refine ⟨28563757016244542446684883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76170018709985446524493021 28563757016244542446684883)
        ·
          refine ⟨42845635524366813670027325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28563757016244542446684883 42845635524366813670027325)
          ·
            refine ⟨16067113321637555126260247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42845635524366813670027325 16067113321637555126260247)
            ·
              refine ⟨24100669982456332689390371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16067113321637555126260247 24100669982456332689390371)
              ·
                refine ⟨36151004973684499034085557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24100669982456332689390371 36151004973684499034085557)
                ·
                  refine ⟨3389156716282921784445521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36151004973684499034085557 3389156716282921784445521)
                  ·
                    refine ⟨2541867537212191338334141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3389156716282921784445521 2541867537212191338334141)
                    ·
                      refine ⟨953200326454571751875303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2541867537212191338334141 953200326454571751875303)
                      ·
                        rfl

theorem cell23_1856351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_1856351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856351 prefixEnd_1856351 := by exact prefixLift 1856351
  have htrace : WordTrace (prefixWord ++ tailWord_1856351) baseStart_1856351 baseEnd_1856351 := by
    simpa [prefixWord, tailWord_1856351, baseEnd_1856351] using wordTrace_append hprefix tailTrace_1856351
  have hstable : (prefixWord ++ tailWord_1856351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856351).length < 2 ^ (prefixWord ++ tailWord_1856351).sum := by decide
  have hdescent : baseEnd_1856351 < baseStart_1856351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856382 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1856382 : Nat := 118140960795 + 1856382 * 2 ^ 59
def prefixEnd_1856382 : Nat := 4983230072969 + 3 ^ 40 * 1856382 * 2
def baseEnd_1856382 : Nat := 953216244354861130587661

theorem tailTrace_1856382 : CollatzResearch.WordTrace tailWord_1856382 prefixEnd_1856382 953216244354861130587661 := by
  unfold tailWord_1856382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463476745081566706185425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45138542640435022432988933 8463476745081566706185425)
  ·
    refine ⟨6347607558811175029639069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8463476745081566706185425 6347607558811175029639069)
    ·
      refine ⟨2380352834554190636114651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6347607558811175029639069 2380352834554190636114651)
      ·
        refine ⟨3570529251831285954171977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380352834554190636114651 3570529251831285954171977)
        ·
          refine ⟨2677896938873464465628983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3570529251831285954171977 2677896938873464465628983)
          ·
            refine ⟨4016845408310196698443475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677896938873464465628983 4016845408310196698443475)
            ·
              refine ⟨6025268112465295047665213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016845408310196698443475 6025268112465295047665213)
              ·
                refine ⟨2259475542174485642874455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6025268112465295047665213 2259475542174485642874455)
                ·
                  refine ⟨3389213313261728464311683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259475542174485642874455 3389213313261728464311683)
                  ·
                    refine ⟨5083819969892592696467525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389213313261728464311683 5083819969892592696467525)
                    ·
                      refine ⟨953216244354861130587661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5083819969892592696467525 953216244354861130587661)
                      ·
                        rfl

theorem cell23_1856382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1856382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856382 prefixEnd_1856382 := by exact prefixLift 1856382
  have htrace : WordTrace (prefixWord ++ tailWord_1856382) baseStart_1856382 baseEnd_1856382 := by
    simpa [prefixWord, tailWord_1856382, baseEnd_1856382] using wordTrace_append hprefix tailTrace_1856382
  have hstable : (prefixWord ++ tailWord_1856382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856382).length < 2 ^ (prefixWord ++ tailWord_1856382).sum := by decide
  have hdescent : baseEnd_1856382 < baseStart_1856382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856384 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 9]
def baseStart_1856384 : Nat := 118140960795 + 1856384 * 2 ^ 59
def prefixEnd_1856384 : Nat := 4983230072969 + 3 ^ 40 * 1856384 * 2
def baseEnd_1856384 : Nat := 317739090438723374254217

theorem tailTrace_1856384 : CollatzResearch.WordTrace tailWord_1856384 prefixEnd_1856384 317739090438723374254217 := by
  unfold tailWord_1856384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33853943453322643995528103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45138591271096858660704137 33853943453322643995528103)
  ·
    refine ⟨50780915179983965993292155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33853943453322643995528103 50780915179983965993292155)
    ·
      refine ⟨76171372769975948989938233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50780915179983965993292155 76171372769975948989938233)
      ·
        refine ⟨57128529577481961742453675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76171372769975948989938233 57128529577481961742453675)
        ·
          refine ⟨85692794366222942613680513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57128529577481961742453675 85692794366222942613680513)
          ·
            refine ⟨64269595774667206960260385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85692794366222942613680513 64269595774667206960260385)
            ·
              refine ⟨48202196831000405220195289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64269595774667206960260385 48202196831000405220195289)
              ·
                refine ⟨36151647623250303915146467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48202196831000405220195289 36151647623250303915146467)
                ·
                  refine ⟨54227471434875455872719701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36151647623250303915146467 54227471434875455872719701)
                  ·
                    refine ⟨317739090438723374254217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 54227471434875455872719701 317739090438723374254217)
                    ·
                      rfl

theorem cell23_1856384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_1856384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856384 prefixEnd_1856384 := by exact prefixLift 1856384
  have htrace : WordTrace (prefixWord ++ tailWord_1856384) baseStart_1856384 baseEnd_1856384 := by
    simpa [prefixWord, tailWord_1856384, baseEnd_1856384] using wordTrace_append hprefix tailTrace_1856384
  have hstable : (prefixWord ++ tailWord_1856384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856384).length < 2 ^ (prefixWord ++ tailWord_1856384).sum := by decide
  have hdescent : baseEnd_1856384 < baseStart_1856384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856412 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1856412 : Nat := 118140960795 + 1856412 * 2 ^ 59
def prefixEnd_1856412 : Nat := 4983230072969 + 3 ^ 40 * 1856412 * 2
def baseEnd_1856412 : Nat := 953231648774496013212523

theorem tailTrace_1856412 : CollatzResearch.WordTrace tailWord_1856412 prefixEnd_1856412 953231648774496013212523 := by
  unfold tailWord_1856412
  simp only [CollatzResearch.WordTrace]
  refine ⟨33854454075271924386537745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45139272100362565848716993 33854454075271924386537745)
  ·
    refine ⟨25390840556453943289903309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33854454075271924386537745 25390840556453943289903309)
    ·
      refine ⟨9521565208670228733713741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25390840556453943289903309 9521565208670228733713741)
      ·
        refine ⟨3570586953251335775142653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9521565208670228733713741 3570586953251335775142653)
        ·
          refine ⟨1338970107469250915678495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3570586953251335775142653 1338970107469250915678495)
          ·
            refine ⟨2008455161203876373517743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338970107469250915678495 2008455161203876373517743)
            ·
              refine ⟨3012682741805814560276615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008455161203876373517743 3012682741805814560276615)
              ·
                refine ⟨4519024112708721840414923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012682741805814560276615 4519024112708721840414923)
                ·
                  refine ⟨6778536169063082760622385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519024112708721840414923 6778536169063082760622385)
                  ·
                    refine ⟨5083902126797312070466789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6778536169063082760622385 5083902126797312070466789)
                    ·
                      refine ⟨953231648774496013212523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5083902126797312070466789 953231648774496013212523)
                      ·
                        rfl

theorem cell23_1856412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1856412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856412 prefixEnd_1856412 := by exact prefixLift 1856412
  have htrace : WordTrace (prefixWord ++ tailWord_1856412) baseStart_1856412 baseEnd_1856412 := by
    simpa [prefixWord, tailWord_1856412, baseEnd_1856412] using wordTrace_append hprefix tailTrace_1856412
  have hstable : (prefixWord ++ tailWord_1856412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856412).length < 2 ^ (prefixWord ++ tailWord_1856412).sum := by decide
  have hdescent : baseEnd_1856412 < baseStart_1856412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856415 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1856415 : Nat := 118140960795 + 1856415 * 2 ^ 59
def prefixEnd_1856415 : Nat := 4983230072969 + 3 ^ 40 * 1856415 * 2
def baseEnd_1856415 : Nat := 953233189216459501475009

theorem tailTrace_1856415 : CollatzResearch.WordTrace tailWord_1856415 prefixEnd_1856415 953233189216459501475009 := by
  unfold tailWord_1856415
  simp only [CollatzResearch.WordTrace]
  refine ⟨67709017569532980285434699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45139345046355320190289799 67709017569532980285434699)
  ·
    refine ⟨101563526354299470428152049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67709017569532980285434699 101563526354299470428152049)
    ·
      refine ⟨76172644765724602821114037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101563526354299470428152049 76172644765724602821114037)
      ·
        refine ⟨7141185446786681514479441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76172644765724602821114037 7141185446786681514479441)
        ·
          refine ⟨5355889085090011135859581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7141185446786681514479441 5355889085090011135859581)
          ·
            refine ⟨2008458406908754175947343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5355889085090011135859581 2008458406908754175947343)
            ·
              refine ⟨3012687610363131263921015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008458406908754175947343 3012687610363131263921015)
              ·
                refine ⟨4519031415544696895881523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012687610363131263921015 4519031415544696895881523)
                ·
                  refine ⟨6778547123317045343822285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519031415544696895881523 6778547123317045343822285)
                  ·
                    refine ⟨2541955171243892003933357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6778547123317045343822285 2541955171243892003933357)
                    ·
                      refine ⟨953233189216459501475009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2541955171243892003933357 953233189216459501475009)
                      ·
                        rfl

theorem cell23_1856415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1856415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856415 prefixEnd_1856415 := by exact prefixLift 1856415
  have htrace : WordTrace (prefixWord ++ tailWord_1856415) baseStart_1856415 baseEnd_1856415 := by
    simpa [prefixWord, tailWord_1856415, baseEnd_1856415] using wordTrace_append hprefix tailTrace_1856415
  have hstable : (prefixWord ++ tailWord_1856415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856415).length < 2 ^ (prefixWord ++ tailWord_1856415).sum := by decide
  have hdescent : baseEnd_1856415 < baseStart_1856415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856425 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 1, 3, 2]
def baseStart_1856425 : Nat := 118140960795 + 1856425 * 2 ^ 59
def prefixEnd_1856425 : Nat := 4983230072969 + 3 ^ 40 * 1856425 * 2
def baseEnd_1856425 : Nat := 953238324023004462349963

theorem tailTrace_1856425 : CollatzResearch.WordTrace tailWord_1856425 prefixEnd_1856425 953238324023004462349963 := by
  unfold tailWord_1856425
  simp only [CollatzResearch.WordTrace]
  refine ⟨67709382299496751993298729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45139588199664501328865819 67709382299496751993298729)
  ·
    refine ⟨50782036724622563994974047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67709382299496751993298729 50782036724622563994974047)
    ·
      refine ⟨76173055086933845992461071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50782036724622563994974047 76173055086933845992461071)
      ·
        refine ⟨114259582630400768988691607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76173055086933845992461071 114259582630400768988691607)
        ·
          refine ⟨171389373945601153483037411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114259582630400768988691607 171389373945601153483037411)
          ·
            refine ⟨257084060918401730224556117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171389373945601153483037411 257084060918401730224556117)
            ·
              refine ⟨3012703838887520276069017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 257084060918401730224556117 3012703838887520276069017)
              ·
                refine ⟨2259527879165640207051763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012703838887520276069017 2259527879165640207051763)
                ·
                  refine ⟨3389291818748460310577645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259527879165640207051763 3389291818748460310577645)
                  ·
                    refine ⟨1270984432030672616466617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389291818748460310577645 1270984432030672616466617)
                    ·
                      refine ⟨953238324023004462349963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1270984432030672616466617 953238324023004462349963)
                      ·
                        rfl

theorem cell23_1856425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 3, 2].length) (baseStart_1856425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856425 prefixEnd_1856425 := by exact prefixLift 1856425
  have htrace : WordTrace (prefixWord ++ tailWord_1856425) baseStart_1856425 baseEnd_1856425 := by
    simpa [prefixWord, tailWord_1856425, baseEnd_1856425] using wordTrace_append hprefix tailTrace_1856425
  have hstable : (prefixWord ++ tailWord_1856425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856425).length < 2 ^ (prefixWord ++ tailWord_1856425).sum := by decide
  have hdescent : baseEnd_1856425 < baseStart_1856425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856441 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1856441 : Nat := 118140960795 + 1856441 * 2 ^ 59
def prefixEnd_1856441 : Nat := 4983230072969 + 3 ^ 40 * 1856441 * 2
def baseEnd_1856441 : Nat := 953246539713476399749889

theorem tailTrace_1856441 : CollatzResearch.WordTrace tailWord_1856441 prefixEnd_1856441 953246539713476399749889 := by
  unfold tailWord_1856441
  simp only [CollatzResearch.WordTrace]
  refine ⟨67709965867438786725881177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45139977244959191150587451 67709965867438786725881177)
  ·
    refine ⟨50782474400579090044410883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67709965867438786725881177 50782474400579090044410883)
    ·
      refine ⟨76173711600868635066616325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50782474400579090044410883 76173711600868635066616325)
      ·
        refine ⟨14282570925162869074990561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76173711600868635066616325 14282570925162869074990561)
        ·
          refine ⟨10711928193872151806242921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14282570925162869074990561 10711928193872151806242921)
          ·
            refine ⟨8033946145404113854682191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10711928193872151806242921 8033946145404113854682191)
            ·
              refine ⟨12050919218106170782023287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8033946145404113854682191 12050919218106170782023287)
              ·
                refine ⟨18076378827159256173034931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12050919218106170782023287 18076378827159256173034931)
                ·
                  refine ⟨27114568240738884259552397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18076378827159256173034931 27114568240738884259552397)
                  ·
                    refine ⟨10167963090277081597332149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27114568240738884259552397 10167963090277081597332149)
                    ·
                      refine ⟨953246539713476399749889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10167963090277081597332149 953246539713476399749889)
                      ·
                        rfl

theorem cell23_1856441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1856441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856441 prefixEnd_1856441 := by exact prefixLift 1856441
  have htrace : WordTrace (prefixWord ++ tailWord_1856441) baseStart_1856441 baseEnd_1856441 := by
    simpa [prefixWord, tailWord_1856441, baseEnd_1856441] using wordTrace_append hprefix tailTrace_1856441
  have hstable : (prefixWord ++ tailWord_1856441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856441).length < 2 ^ (prefixWord ++ tailWord_1856441).sum := by decide
  have hdescent : baseEnd_1856441 < baseStart_1856441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856455 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_1856455 : Nat := 118140960795 + 1856455 * 2 ^ 59
def prefixEnd_1856455 : Nat := 4983230072969 + 3 ^ 40 * 1856455 * 2
def baseEnd_1856455 : Nat := 953253728442639344974825

theorem tailTrace_1856455 : CollatzResearch.WordTrace tailWord_1856455 prefixEnd_1856455 953253728442639344974825 := by
  unfold tailWord_1856455
  simp only [CollatzResearch.WordTrace]
  refine ⟨67710476489388067116890819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45140317659592044744593879 67710476489388067116890819)
  ·
    refine ⟨101565714734082100675336229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67710476489388067116890819 101565714734082100675336229)
    ·
      refine ⟨19043571512640393876625543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101565714734082100675336229 19043571512640393876625543)
      ·
        refine ⟨28565357268960590814938315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19043571512640393876625543 28565357268960590814938315)
        ·
          refine ⟨42848035903440886222407473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28565357268960590814938315 42848035903440886222407473)
          ·
            refine ⟨32136026927580664666805605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42848035903440886222407473 32136026927580664666805605)
            ·
              refine ⟨6025505048921374625026051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32136026927580664666805605 6025505048921374625026051)
              ·
                refine ⟨9038257573382061937539077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025505048921374625026051 9038257573382061937539077)
                ·
                  refine ⟨1694673295009136613288577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9038257573382061937539077 1694673295009136613288577)
                  ·
                    refine ⟨1271004971256852459966433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694673295009136613288577 1271004971256852459966433)
                    ·
                      refine ⟨953253728442639344974825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271004971256852459966433 953253728442639344974825)
                      ·
                        rfl

theorem cell23_1856455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_1856455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856455 prefixEnd_1856455 := by exact prefixLift 1856455
  have htrace : WordTrace (prefixWord ++ tailWord_1856455) baseStart_1856455 baseEnd_1856455 := by
    simpa [prefixWord, tailWord_1856455, baseEnd_1856455] using wordTrace_append hprefix tailTrace_1856455
  have hstable : (prefixWord ++ tailWord_1856455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856455).length < 2 ^ (prefixWord ++ tailWord_1856455).sum := by decide
  have hdescent : baseEnd_1856455 < baseStart_1856455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856472 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 2, 2, 2]
def baseStart_1856472 : Nat := 118140960795 + 1856472 * 2 ^ 59
def prefixEnd_1856472 : Nat := 4983230072969 + 3 ^ 40 * 1856472 * 2
def baseEnd_1856472 : Nat := 953262457613765778462247

theorem tailTrace_1856472 : CollatzResearch.WordTrace tailWord_1856472 prefixEnd_1856472 953262457613765778462247 := by
  unfold tailWord_1856472
  simp only [CollatzResearch.WordTrace]
  refine ⟨33855548265163239510129835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45140731020217652680173113 33855548265163239510129835)
  ·
    refine ⟨50783322397744859265194753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33855548265163239510129835 50783322397744859265194753)
    ·
      refine ⟨38087491798308644448896065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50783322397744859265194753 38087491798308644448896065)
      ·
        refine ⟨28565618848731483336672049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38087491798308644448896065 28565618848731483336672049)
        ·
          refine ⟨21424214136548612502504037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28565618848731483336672049 21424214136548612502504037)
          ·
            refine ⟨4017040150602864844219507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21424214136548612502504037 4017040150602864844219507)
            ·
              refine ⟨6025560225904297266329261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017040150602864844219507 6025560225904297266329261)
              ·
                refine ⟨2259585084714111474873473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6025560225904297266329261 2259585084714111474873473)
                ·
                  refine ⟨1694688813535583606155105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259585084714111474873473 1694688813535583606155105)
                  ·
                    refine ⟨1271016610151687704616329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694688813535583606155105 1271016610151687704616329)
                    ·
                      refine ⟨953262457613765778462247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271016610151687704616329 953262457613765778462247)
                      ·
                        rfl

theorem cell23_1856472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_1856472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856472 prefixEnd_1856472 := by exact prefixLift 1856472
  have htrace : WordTrace (prefixWord ++ tailWord_1856472) baseStart_1856472 baseEnd_1856472 := by
    simpa [prefixWord, tailWord_1856472, baseEnd_1856472] using wordTrace_append hprefix tailTrace_1856472
  have hstable : (prefixWord ++ tailWord_1856472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856472).length < 2 ^ (prefixWord ++ tailWord_1856472).sum := by decide
  have hdescent : baseEnd_1856472 < baseStart_1856472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856508 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_1856508 : Nat := 118140960795 + 1856508 * 2 ^ 59
def prefixEnd_1856508 : Nat := 4983230072969 + 3 ^ 40 * 1856508 * 2
def baseEnd_1856508 : Nat := 317760314305775879204027

theorem tailTrace_1856508 : CollatzResearch.WordTrace tailWord_1856508 prefixEnd_1856508 317760314305775879204027 := by
  unfold tailWord_1856508
  simp only [CollatzResearch.WordTrace]
  refine ⟨33856204779098028584285089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45141606372130704779046785 33856204779098028584285089)
  ·
    refine ⟨25392153584323521438213817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33856204779098028584285089 25392153584323521438213817)
    ·
      refine ⟨19044115188242641078660363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25392153584323521438213817 19044115188242641078660363)
      ·
        refine ⟨28566172782363961617990545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19044115188242641078660363 28566172782363961617990545)
        ·
          refine ⟨21424629586772971213492909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28566172782363961617990545 21424629586772971213492909)
          ·
            refine ⟨8034236095039864205059841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21424629586772971213492909 8034236095039864205059841)
            ·
              refine ⟨6025677071279898153794881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034236095039864205059841 6025677071279898153794881)
              ·
                refine ⟨4519257803459923615346161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025677071279898153794881 4519257803459923615346161)
                ·
                  refine ⟨3389443352594942711509621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4519257803459923615346161 3389443352594942711509621)
                  ·
                    refine ⟨317760314305775879204027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3389443352594942711509621 317760314305775879204027)
                    ·
                      rfl

theorem cell23_1856508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_1856508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856508 prefixEnd_1856508 := by exact prefixLift 1856508
  have htrace : WordTrace (prefixWord ++ tailWord_1856508) baseStart_1856508 baseEnd_1856508 := by
    simpa [prefixWord, tailWord_1856508, baseEnd_1856508] using wordTrace_append hprefix tailTrace_1856508
  have hstable : (prefixWord ++ tailWord_1856508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856508).length < 2 ^ (prefixWord ++ tailWord_1856508).sum := by decide
  have hdescent : baseEnd_1856508 < baseStart_1856508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856511 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_1856511 : Nat := 118140960795 + 1856511 * 2 ^ 59
def prefixEnd_1856511 : Nat := 4983230072969 + 3 ^ 40 * 1856511 * 2
def baseEnd_1856511 : Nat := 953282483359291125874567

theorem tailTrace_1856511 : CollatzResearch.WordTrace tailWord_1856511 prefixEnd_1856511 953282483359291125874567 := by
  unfold tailWord_1856511
  simp only [CollatzResearch.WordTrace]
  refine ⟨67712518977185188680929387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45141679318123459120619591 67712518977185188680929387)
  ·
    refine ⟨101568778465777783021394081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67712518977185188680929387 101568778465777783021394081)
    ·
      refine ⟨76176583849333337266045561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101568778465777783021394081 76176583849333337266045561)
      ·
        refine ⟨57132437887000002949534171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76176583849333337266045561 57132437887000002949534171)
        ·
          refine ⟨85698656830500004424301257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57132437887000002949534171 85698656830500004424301257)
          ·
            refine ⟨64273992622875003318225943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85698656830500004424301257 64273992622875003318225943)
            ·
              refine ⟨96410988934312504977338915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64273992622875003318225943 96410988934312504977338915)
              ·
                refine ⟨144616483401468757466008373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96410988934312504977338915 144616483401468757466008373)
                ·
                  refine ⟨13557795318887696012438285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144616483401468757466008373 13557795318887696012438285)
                  ·
                    refine ⟨5084173244582886004664357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13557795318887696012438285 5084173244582886004664357)
                    ·
                      refine ⟨953282483359291125874567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5084173244582886004664357 953282483359291125874567)
                      ·
                        rfl

theorem cell23_1856511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_1856511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856511 prefixEnd_1856511 := by exact prefixLift 1856511
  have htrace : WordTrace (prefixWord ++ tailWord_1856511) baseStart_1856511 baseEnd_1856511 := by
    simpa [prefixWord, tailWord_1856511, baseEnd_1856511] using wordTrace_append hprefix tailTrace_1856511
  have hstable : (prefixWord ++ tailWord_1856511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856511).length < 2 ^ (prefixWord ++ tailWord_1856511).sum := by decide
  have hdescent : baseEnd_1856511 < baseStart_1856511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856545 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1856545 : Nat := 118140960795 + 1856545 * 2 ^ 59
def prefixEnd_1856545 : Nat := 4983230072969 + 3 ^ 40 * 1856545 * 2
def baseEnd_1856545 : Nat := 953299941701543992849411

theorem tailTrace_1856545 : CollatzResearch.WordTrace tailWord_1856545 prefixEnd_1856545 953299941701543992849411 := by
  unfold tailWord_1856545
  simp only [CollatzResearch.WordTrace]
  refine ⟨67713759059062012487667089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45142506039374674991778059 67713759059062012487667089)
  ·
    refine ⟨50785319294296509365750317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67713759059062012487667089 50785319294296509365750317)
    ·
      refine ⟨19044494735361191012156369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50785319294296509365750317 19044494735361191012156369)
      ·
        refine ⟨14283371051520893259117277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19044494735361191012156369 14283371051520893259117277)
        ·
          refine ⟨5356264144320334972168979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14283371051520893259117277 5356264144320334972168979)
          ·
            refine ⟨8034396216480502458253469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356264144320334972168979 8034396216480502458253469)
            ·
              refine ⟨3012898581180188421845051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8034396216480502458253469 3012898581180188421845051)
              ·
                refine ⟨4519347871770282632767577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012898581180188421845051 4519347871770282632767577)
                ·
                  refine ⟨3389510903827711974575683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4519347871770282632767577 3389510903827711974575683)
                  ·
                    refine ⟨5084266355741567961863525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389510903827711974575683 5084266355741567961863525)
                    ·
                      refine ⟨953299941701543992849411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5084266355741567961863525 953299941701543992849411)
                      ·
                        rfl

theorem cell23_1856545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1856545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856545 prefixEnd_1856545 := by exact prefixLift 1856545
  have htrace : WordTrace (prefixWord ++ tailWord_1856545) baseStart_1856545 baseEnd_1856545 := by
    simpa [prefixWord, tailWord_1856545, baseEnd_1856545] using wordTrace_append hprefix tailTrace_1856545
  have hstable : (prefixWord ++ tailWord_1856545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856545).length < 2 ^ (prefixWord ++ tailWord_1856545).sum := by decide
  have hdescent : baseEnd_1856545 < baseStart_1856545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856558 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1856558 : Nat := 118140960795 + 1856558 * 2 ^ 59
def prefixEnd_1856558 : Nat := 4983230072969 + 3 ^ 40 * 1856558 * 2
def baseEnd_1856558 : Nat := 953306616950052441986851

theorem tailTrace_1856558 : CollatzResearch.WordTrace tailWord_1856558 prefixEnd_1856558 953306616950052441986851 := by
  unfold tailWord_1856558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464279151001864463486291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45142822138676610471926885 8464279151001864463486291)
  ·
    refine ⟨12696418726502796695229437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8464279151001864463486291 12696418726502796695229437)
    ·
      refine ⟨4761157022438548760711039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12696418726502796695229437 4761157022438548760711039)
      ·
        refine ⟨7141735533657823141066559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4761157022438548760711039 7141735533657823141066559)
        ·
          refine ⟨10712603300486734711599839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141735533657823141066559 10712603300486734711599839)
          ·
            refine ⟨16068904950730102067399759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10712603300486734711599839 16068904950730102067399759)
            ·
              refine ⟨24103357426095153101099639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16068904950730102067399759 24103357426095153101099639)
              ·
                refine ⟨36155036139142729651649459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24103357426095153101099639 36155036139142729651649459)
                ·
                  refine ⟨54232554208714094477474189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36155036139142729651649459 54232554208714094477474189)
                  ·
                    refine ⟨20337207828267785429052821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54232554208714094477474189 20337207828267785429052821)
                    ·
                      refine ⟨953306616950052441986851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20337207828267785429052821 953306616950052441986851)
                      ·
                        rfl

theorem cell23_1856558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1856558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856558 prefixEnd_1856558 := by exact prefixLift 1856558
  have htrace : WordTrace (prefixWord ++ tailWord_1856558) baseStart_1856558 baseEnd_1856558 := by
    simpa [prefixWord, tailWord_1856558, baseEnd_1856558] using wordTrace_append hprefix tailTrace_1856558
  have hstable : (prefixWord ++ tailWord_1856558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856558).length < 2 ^ (prefixWord ++ tailWord_1856558).sum := by decide
  have hdescent : baseEnd_1856558 < baseStart_1856558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856568 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 8]
def baseStart_1856568 : Nat := 118140960795 + 1856568 * 2 ^ 59
def prefixEnd_1856568 : Nat := 4983230072969 + 3 ^ 40 * 1856568 * 2
def baseEnd_1856568 : Nat := 105923527972955266984645

theorem tailTrace_1856568 : CollatzResearch.WordTrace tailWord_1856568 prefixEnd_1856568 105923527972955266984645 := by
  unfold tailWord_1856568
  simp only [CollatzResearch.WordTrace]
  refine ⟨33857298968989343707877179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45143065291985791610502905 33857298968989343707877179)
  ·
    refine ⟨50785948453484015561815769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33857298968989343707877179 50785948453484015561815769)
    ·
      refine ⟨38089461340113011671361827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50785948453484015561815769 38089461340113011671361827)
      ·
        refine ⟨57134192010169517507042741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38089461340113011671361827 57134192010169517507042741)
        ·
          refine ⟨5356330500953392266285257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57134192010169517507042741 5356330500953392266285257)
          ·
            refine ⟨4017247875715044199713943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5356330500953392266285257 4017247875715044199713943)
            ·
              refine ⟨6025871813572566299570915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017247875715044199713943 6025871813572566299570915)
              ·
                refine ⟨9038807720358849449356373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025871813572566299570915 9038807720358849449356373)
                ·
                  refine ⟨105923527972955266984645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9038807720358849449356373 105923527972955266984645)
                  ·
                    rfl

theorem cell23_1856568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 8].length) (baseStart_1856568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856568 prefixEnd_1856568 := by exact prefixLift 1856568
  have htrace : WordTrace (prefixWord ++ tailWord_1856568) baseStart_1856568 baseEnd_1856568 := by
    simpa [prefixWord, tailWord_1856568, baseEnd_1856568] using wordTrace_append hprefix tailTrace_1856568
  have hstable : (prefixWord ++ tailWord_1856568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856568).length < 2 ^ (prefixWord ++ tailWord_1856568).sum := by decide
  have hdescent : baseEnd_1856568 < baseStart_1856568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856572 : List Nat := [2, 2, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_1856572 : Nat := 118140960795 + 1856572 * 2 ^ 59
def prefixEnd_1856572 : Nat := 4983230072969 + 3 ^ 40 * 1856572 * 2
def baseEnd_1856572 : Nat := 317771268559738462403929

theorem tailTrace_1856572 : CollatzResearch.WordTrace tailWord_1856572 prefixEnd_1856572 317771268559738462403929 := by
  unfold tailWord_1856572
  simp only [CollatzResearch.WordTrace]
  refine ⟨33857371914982098049449985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45143162553309464065933313 33857371914982098049449985)
  ·
    refine ⟨25393028936236573537087489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33857371914982098049449985 25393028936236573537087489)
    ·
      refine ⟨19044771702177430152815617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25393028936236573537087489 19044771702177430152815617)
      ·
        refine ⟨14283578776633072614611713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19044771702177430152815617 14283578776633072614611713)
        ·
          refine ⟨10712684082474804460958785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14283578776633072614611713 10712684082474804460958785)
          ·
            refine ⟨8034513061856103345719089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10712684082474804460958785 8034513061856103345719089)
            ·
              refine ⟨6025884796392077509289317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034513061856103345719089 6025884796392077509289317)
              ·
                refine ⟨1129853399323514532991747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6025884796392077509289317 1129853399323514532991747)
                ·
                  refine ⟨1694780098985271799487621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1129853399323514532991747 1694780098985271799487621)
                  ·
                    refine ⟨317771268559738462403929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1694780098985271799487621 317771268559738462403929)
                    ·
                      rfl

theorem cell23_1856572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_1856572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856572 prefixEnd_1856572 := by exact prefixLift 1856572
  have htrace : WordTrace (prefixWord ++ tailWord_1856572) baseStart_1856572 baseEnd_1856572 := by
    simpa [prefixWord, tailWord_1856572, baseEnd_1856572] using wordTrace_append hprefix tailTrace_1856572
  have hstable : (prefixWord ++ tailWord_1856572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856572).length < 2 ^ (prefixWord ++ tailWord_1856572).sum := by decide
  have hdescent : baseEnd_1856572 < baseStart_1856572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856582 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1856582 : Nat := 118140960795 + 1856582 * 2 ^ 59
def prefixEnd_1856582 : Nat := 4983230072969 + 3 ^ 40 * 1856582 * 2
def baseEnd_1856582 : Nat := 953318940485760348086741

theorem tailTrace_1856582 : CollatzResearch.WordTrace tailWord_1856582 prefixEnd_1856582 953318940485760348086741 := by
  unfold tailWord_1856582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116097142497748993961375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45143405706618645204509333 2116097142497748993961375)
  ·
    refine ⟨3174145713746623490942063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2116097142497748993961375 3174145713746623490942063)
    ·
      refine ⟨4761218570619935236413095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174145713746623490942063 4761218570619935236413095)
      ·
        refine ⟨7141827855929902854619643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4761218570619935236413095 7141827855929902854619643)
        ·
          refine ⟨10712741783894854281929465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141827855929902854619643 10712741783894854281929465)
          ·
            refine ⟨8034556337921140711447099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10712741783894854281929465 8034556337921140711447099)
            ·
              refine ⟨12051834506881711067170649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8034556337921140711447099 12051834506881711067170649)
              ·
                refine ⟨9038875880161283300377987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12051834506881711067170649 9038875880161283300377987)
                ·
                  refine ⟨13558313820241924950566981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9038875880161283300377987 13558313820241924950566981)
                  ·
                    refine ⟨2542183841295360928231309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13558313820241924950566981 2542183841295360928231309)
                    ·
                      refine ⟨953318940485760348086741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2542183841295360928231309 953318940485760348086741)
                      ·
                        rfl

theorem cell23_1856582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1856582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856582 prefixEnd_1856582 := by exact prefixLift 1856582
  have htrace : WordTrace (prefixWord ++ tailWord_1856582) baseStart_1856582 baseEnd_1856582 := by
    simpa [prefixWord, tailWord_1856582, baseEnd_1856582] using wordTrace_append hprefix tailTrace_1856582
  have hstable : (prefixWord ++ tailWord_1856582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856582).length < 2 ^ (prefixWord ++ tailWord_1856582).sum := by decide
  have hdescent : baseEnd_1856582 < baseStart_1856582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856615 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 1, 5]
def baseStart_1856615 : Nat := 118140960795 + 1856615 * 2 ^ 59
def prefixEnd_1856615 : Nat := 4983230072969 + 3 ^ 40 * 1856615 * 2
def baseEnd_1856615 : Nat := 317778628449119572991363

theorem tailTrace_1856615 : CollatzResearch.WordTrace tailWord_1856615 prefixEnd_1856615 317778628449119572991363 := by
  unfold tailWord_1856615
  simp only [CollatzResearch.WordTrace]
  refine ⟨67716312168808414442715299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45144208112538942961810199 67716312168808414442715299)
  ·
    refine ⟨101574468253212621664072949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67716312168808414442715299 101574468253212621664072949)
    ·
      refine ⟨9522606398738683281006839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101574468253212621664072949 9522606398738683281006839)
      ·
        refine ⟨14283909598108024921510259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9522606398738683281006839 14283909598108024921510259)
        ·
          refine ⟨21425864397162037382265389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14283909598108024921510259 21425864397162037382265389)
          ·
            refine ⟨8034699148935764018349521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21425864397162037382265389 8034699148935764018349521)
            ·
              refine ⟨6026024361701823013762141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034699148935764018349521 6026024361701823013762141)
              ·
                refine ⟨2259759135638183630160803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6026024361701823013762141 2259759135638183630160803)
                ·
                  refine ⟨3389638703457275445241205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2259759135638183630160803 3389638703457275445241205)
                  ·
                    refine ⟨317778628449119572991363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3389638703457275445241205 317778628449119572991363)
                    ·
                      rfl

theorem cell23_1856615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_1856615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856615 prefixEnd_1856615 := by exact prefixLift 1856615
  have htrace : WordTrace (prefixWord ++ tailWord_1856615) baseStart_1856615 baseEnd_1856615 := by
    simpa [prefixWord, tailWord_1856615, baseEnd_1856615] using wordTrace_append hprefix tailTrace_1856615
  have hstable : (prefixWord ++ tailWord_1856615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856615).length < 2 ^ (prefixWord ++ tailWord_1856615).sum := by decide
  have hdescent : baseEnd_1856615 < baseStart_1856615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856622 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_1856622 : Nat := 118140960795 + 1856622 * 2 ^ 59
def prefixEnd_1856622 : Nat := 4983230072969 + 3 ^ 40 * 1856622 * 2
def baseEnd_1856622 : Nat := 953339479711940191586557

theorem tailTrace_1856622 : CollatzResearch.WordTrace tailWord_1856622 prefixEnd_1856622 953339479711940191586557 := by
  unfold tailWord_1856622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464570934972881829777515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45144378319855369758813413 8464570934972881829777515)
  ·
    refine ⟨12696856402459322744666273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8464570934972881829777515 12696856402459322744666273)
    ·
      refine ⟨9522642301844492058499705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12696856402459322744666273 9522642301844492058499705)
      ·
        refine ⟨7141981726383369043874779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9522642301844492058499705 7141981726383369043874779)
        ·
          refine ⟨10712972589575053565812169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141981726383369043874779 10712972589575053565812169)
          ·
            refine ⟨8034729442181290174359127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10712972589575053565812169 8034729442181290174359127)
            ·
              refine ⟨12052094163271935261538691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8034729442181290174359127 12052094163271935261538691)
              ·
                refine ⟨18078141244907902892308037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12052094163271935261538691 18078141244907902892308037)
                ·
                  refine ⟨3389651483420231792307757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18078141244907902892308037 3389651483420231792307757)
                  ·
                    refine ⟨1271119306282586922115409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389651483420231792307757 1271119306282586922115409)
                    ·
                      refine ⟨953339479711940191586557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271119306282586922115409 953339479711940191586557)
                      ·
                        rfl

theorem cell23_1856622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_1856622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856622 prefixEnd_1856622 := by exact prefixLift 1856622
  have htrace : WordTrace (prefixWord ++ tailWord_1856622) baseStart_1856622 baseEnd_1856622 := by
    simpa [prefixWord, tailWord_1856622, baseEnd_1856622] using wordTrace_append hprefix tailTrace_1856622
  have hstable : (prefixWord ++ tailWord_1856622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856622).length < 2 ^ (prefixWord ++ tailWord_1856622).sum := by decide
  have hdescent : baseEnd_1856622 < baseStart_1856622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856652 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 3, 2, 2]
def baseStart_1856652 : Nat := 118140960795 + 1856652 * 2 ^ 59
def prefixEnd_1856652 : Nat := 4983230072969 + 3 ^ 40 * 1856652 * 2
def baseEnd_1856652 : Nat := 953354884131575074211419

theorem tailTrace_1856652 : CollatzResearch.WordTrace tailWord_1856652 prefixEnd_1856652 953354884131575074211419 := by
  unfold tailWord_1856652
  simp only [CollatzResearch.WordTrace]
  refine ⟨33858830834837184880906105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45145107779782913174541473 33858830834837184880906105)
  ·
    refine ⟨25394123126127888660679579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33858830834837184880906105 25394123126127888660679579)
    ·
      refine ⟨38091184689191832991019369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25394123126127888660679579 38091184689191832991019369)
      ·
        refine ⟨28568388516893874743264527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38091184689191832991019369 28568388516893874743264527)
        ·
          refine ⟨42852582775340812114896791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28568388516893874743264527 42852582775340812114896791)
          ·
            refine ⟨64278874163011218172345187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42852582775340812114896791 64278874163011218172345187)
            ·
              refine ⟨96418311244516827258517781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64278874163011218172345187 96418311244516827258517781)
              ·
                refine ⟨4519608339586726277743021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96418311244516827258517781 4519608339586726277743021)
                ·
                  refine ⟨1694853127345022354153633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4519608339586726277743021 1694853127345022354153633)
                  ·
                    refine ⟨1271139845508766765615225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694853127345022354153633 1271139845508766765615225)
                    ·
                      refine ⟨953354884131575074211419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271139845508766765615225 953354884131575074211419)
                      ·
                        rfl

theorem cell23_1856652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_1856652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856652 prefixEnd_1856652 := by exact prefixLift 1856652
  have htrace : WordTrace (prefixWord ++ tailWord_1856652) baseStart_1856652 baseEnd_1856652 := by
    simpa [prefixWord, tailWord_1856652, baseEnd_1856652] using wordTrace_append hprefix tailTrace_1856652
  have hstable : (prefixWord ++ tailWord_1856652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856652).length < 2 ^ (prefixWord ++ tailWord_1856652).sum := by decide
  have hdescent : baseEnd_1856652 < baseStart_1856652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856679 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 2, 4]
def baseStart_1856679 : Nat := 118140960795 + 1856679 * 2 ^ 59
def prefixEnd_1856679 : Nat := 4983230072969 + 3 ^ 40 * 1856679 * 2
def baseEnd_1856679 : Nat := 317789582703082156191265

theorem tailTrace_1856679 : CollatzResearch.WordTrace tailWord_1856679 prefixEnd_1856679 317789582703082156191265 := by
  unfold tailWord_1856679
  simp only [CollatzResearch.WordTrace]
  refine ⟨67718646440576553373045091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45145764293717702248696727 67718646440576553373045091)
  ·
    refine ⟨101577969660864830059567637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67718646440576553373045091 101577969660864830059567637)
    ·
      refine ⟨4761467327853038909042233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101577969660864830059567637 4761467327853038909042233)
      ·
        refine ⟨3571100495889779181781675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761467327853038909042233 3571100495889779181781675)
        ·
          refine ⟨5356650743834668772672513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571100495889779181781675 5356650743834668772672513)
          ·
            refine ⟨4017488057876001579504385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5356650743834668772672513 4017488057876001579504385)
            ·
              refine ⟨3013116043407001184628289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017488057876001579504385 3013116043407001184628289)
              ·
                refine ⟨2259837032555250888471217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013116043407001184628289 2259837032555250888471217)
                ·
                  refine ⟨1694877774416438166353413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259837032555250888471217 1694877774416438166353413)
                  ·
                    refine ⟨317789582703082156191265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1694877774416438166353413 317789582703082156191265)
                    ·
                      rfl

theorem cell23_1856679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_1856679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856679 prefixEnd_1856679 := by exact prefixLift 1856679
  have htrace : WordTrace (prefixWord ++ tailWord_1856679) baseStart_1856679 baseEnd_1856679 := by
    simpa [prefixWord, tailWord_1856679, baseEnd_1856679] using wordTrace_append hprefix tailTrace_1856679
  have hstable : (prefixWord ++ tailWord_1856679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856679).length < 2 ^ (prefixWord ++ tailWord_1856679).sum := by decide
  have hdescent : baseEnd_1856679 < baseStart_1856679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856698 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1856698 : Nat := 118140960795 + 1856698 * 2 ^ 59
def prefixEnd_1856698 : Nat := 4983230072969 + 3 ^ 40 * 1856698 * 2
def baseEnd_1856698 : Nat := 953378504241681894236207

theorem tailTrace_1856698 : CollatzResearch.WordTrace tailWord_1856698 prefixEnd_1856698 953378504241681894236207 := by
  unfold tailWord_1856698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16929834856876929904496687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45146226285005146411991165 16929834856876929904496687)
  ·
    refine ⟨25394752285315394856745031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16929834856876929904496687 25394752285315394856745031)
    ·
      refine ⟨38092128427973092285117547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25394752285315394856745031 38092128427973092285117547)
      ·
        refine ⟨57138192641959638427676321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38092128427973092285117547 57138192641959638427676321)
        ·
          refine ⟨42853644481469728820757241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57138192641959638427676321 42853644481469728820757241)
          ·
            refine ⟨32140233361102296615567931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42853644481469728820757241 32140233361102296615567931)
            ·
              refine ⟨48210350041653444923351897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32140233361102296615567931 48210350041653444923351897)
              ·
                refine ⟨36157762531240083692513923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48210350041653444923351897 36157762531240083692513923)
                ·
                  refine ⟨54236643796860125538770885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36157762531240083692513923 54236643796860125538770885)
                  ·
                    refine ⟨10169370711911273538519541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54236643796860125538770885 10169370711911273538519541)
                    ·
                      refine ⟨953378504241681894236207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10169370711911273538519541 953378504241681894236207)
                      ·
                        rfl

theorem cell23_1856698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1856698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856698 prefixEnd_1856698 := by exact prefixLift 1856698
  have htrace : WordTrace (prefixWord ++ tailWord_1856698) baseStart_1856698 baseEnd_1856698 := by
    simpa [prefixWord, tailWord_1856698, baseEnd_1856698] using wordTrace_append hprefix tailTrace_1856698
  have hstable : (prefixWord ++ tailWord_1856698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856698).length < 2 ^ (prefixWord ++ tailWord_1856698).sum := by decide
  have hdescent : baseEnd_1856698 < baseStart_1856698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856702 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1856702 : Nat := 118140960795 + 1856702 * 2 ^ 59
def prefixEnd_1856702 : Nat := 4983230072969 + 3 ^ 40 * 1856702 * 2
def baseEnd_1856702 : Nat := 953380558164299878586189

theorem tailTrace_1856702 : CollatzResearch.WordTrace tailWord_1856702 prefixEnd_1856702 953380558164299878586189 := by
  unfold tailWord_1856702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464935664936653537641545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45146323546328818867421573 8464935664936653537641545)
  ·
    refine ⟨6348701748702490153231159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8464935664936653537641545 6348701748702490153231159)
    ·
      refine ⟨9523052623053735229846739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6348701748702490153231159 9523052623053735229846739)
      ·
        refine ⟨14284578934580602844770109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9523052623053735229846739 14284578934580602844770109)
        ·
          refine ⟨5356717100467726066788791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14284578934580602844770109 5356717100467726066788791)
          ·
            refine ⟨8035075650701589100183187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356717100467726066788791 8035075650701589100183187)
            ·
              refine ⟨12052613476052383650274781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035075650701589100183187 12052613476052383650274781)
              ·
                refine ⟨4519730053519643868853043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12052613476052383650274781 4519730053519643868853043)
                ·
                  refine ⟨6779595080279465803279565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519730053519643868853043 6779595080279465803279565)
                  ·
                    refine ⟨2542348155104799676229837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6779595080279465803279565 2542348155104799676229837)
                    ·
                      refine ⟨953380558164299878586189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2542348155104799676229837 953380558164299878586189)
                      ·
                        rfl

theorem cell23_1856702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1856702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856702 prefixEnd_1856702 := by exact prefixLift 1856702
  have htrace : WordTrace (prefixWord ++ tailWord_1856702) baseStart_1856702 baseEnd_1856702 := by
    simpa [prefixWord, tailWord_1856702, baseEnd_1856702] using wordTrace_append hprefix tailTrace_1856702
  have hstable : (prefixWord ++ tailWord_1856702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856702).length < 2 ^ (prefixWord ++ tailWord_1856702).sum := by decide
  have hdescent : baseEnd_1856702 < baseStart_1856702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856712 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_1856712 : Nat := 118140960795 + 1856712 * 2 ^ 59
def prefixEnd_1856712 : Nat := 4983230072969 + 3 ^ 40 * 1856712 * 2
def baseEnd_1856712 : Nat := 953385692970844839461143

theorem tailTrace_1856712 : CollatzResearch.WordTrace tailWord_1856712 prefixEnd_1856712 953385692970844839461143 := by
  unfold tailWord_1856712
  simp only [CollatzResearch.WordTrace]
  refine ⟨33859925024728500004498195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45146566699638000005997593 33859925024728500004498195)
  ·
    refine ⟨50789887537092750006747293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33859925024728500004498195 50789887537092750006747293)
    ·
      refine ⟨19046207826409781252530235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50789887537092750006747293 19046207826409781252530235)
      ·
        refine ⟨28569311739614671878795353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19046207826409781252530235 28569311739614671878795353)
        ·
          refine ⟨21426983804711003909096515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28569311739614671878795353 21426983804711003909096515)
          ·
            refine ⟨32140475707066505863644773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21426983804711003909096515 32140475707066505863644773)
            ·
              refine ⟨6026339195074969849433395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32140475707066505863644773 6026339195074969849433395)
              ·
                refine ⟨9039508792612454774150093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026339195074969849433395 9039508792612454774150093)
                ·
                  refine ⟨3389815797229670540306285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9039508792612454774150093 3389815797229670540306285)
                  ·
                    refine ⟨1271180923961126452614857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389815797229670540306285 1271180923961126452614857)
                    ·
                      refine ⟨953385692970844839461143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271180923961126452614857 953385692970844839461143)
                      ·
                        rfl

theorem cell23_1856712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_1856712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856712 prefixEnd_1856712 := by exact prefixLift 1856712
  have htrace : WordTrace (prefixWord ++ tailWord_1856712) baseStart_1856712 baseEnd_1856712 := by
    simpa [prefixWord, tailWord_1856712, baseEnd_1856712] using wordTrace_append hprefix tailTrace_1856712
  have hstable : (prefixWord ++ tailWord_1856712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856712).length < 2 ^ (prefixWord ++ tailWord_1856712).sum := by decide
  have hdescent : baseEnd_1856712 < baseStart_1856712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856755 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4]
def baseStart_1856755 : Nat := 118140960795 + 1856755 * 2 ^ 59
def prefixEnd_1856755 : Nat := 4983230072969 + 3 ^ 40 * 1856755 * 2
def baseEnd_1856755 : Nat := 953407772638988171223445

theorem tailTrace_1856755 : CollatzResearch.WordTrace tailWord_1856755 prefixEnd_1856755 953407772638988171223445 := by
  unfold tailWord_1856755
  simp only [CollatzResearch.WordTrace]
  refine ⟨67721418388301218352811719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45147612258867478901874479 67721418388301218352811719)
  ·
    refine ⟨101582127582451827529217579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67721418388301218352811719 101582127582451827529217579)
    ·
      refine ⟨152373191373677741293826369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101582127582451827529217579 152373191373677741293826369)
      ·
        refine ⟨114279893530258305970369777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152373191373677741293826369 114279893530258305970369777)
        ·
          refine ⟨85709920147693729477777333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114279893530258305970369777 85709920147693729477777333)
          ·
            refine ⟨8035305013846287138541625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85709920147693729477777333 8035305013846287138541625)
            ·
              refine ⟨6026478760384715353906219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8035305013846287138541625 6026478760384715353906219)
              ·
                refine ⟨9039718140577073030859329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026478760384715353906219 9039718140577073030859329)
                ·
                  refine ⟨6779788605432804773144497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9039718140577073030859329 6779788605432804773144497)
                  ·
                    refine ⟨5084841454074603579858373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6779788605432804773144497 5084841454074603579858373)
                    ·
                      refine ⟨953407772638988171223445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5084841454074603579858373 953407772638988171223445)
                      ·
                        rfl

theorem cell23_1856755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_1856755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856755 prefixEnd_1856755 := by exact prefixLift 1856755
  have htrace : WordTrace (prefixWord ++ tailWord_1856755) baseStart_1856755 baseEnd_1856755 := by
    simpa [prefixWord, tailWord_1856755, baseEnd_1856755] using wordTrace_append hprefix tailTrace_1856755
  have hstable : (prefixWord ++ tailWord_1856755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856755).length < 2 ^ (prefixWord ++ tailWord_1856755).sum := by decide
  have hdescent : baseEnd_1856755 < baseStart_1856755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856799 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 7]
def baseStart_1856799 : Nat := 118140960795 + 1856799 * 2 ^ 59
def prefixEnd_1856799 : Nat := 4983230072969 + 3 ^ 40 * 1856799 * 2
def baseEnd_1856799 : Nat := 105936707309753999897027

theorem tailTrace_1856799 : CollatzResearch.WordTrace tailWord_1856799 prefixEnd_1856799 105936707309753999897027 := by
  unfold tailWord_1856799
  simp only [CollatzResearch.WordTrace]
  refine ⟨67723023200141813867413451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45148682133427875911608967 67723023200141813867413451)
  ·
    refine ⟨101584534800212720801120177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67723023200141813867413451 101584534800212720801120177)
    ·
      refine ⟨76188401100159540600840133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101584534800212720801120177 76188401100159540600840133)
      ·
        refine ⟨14285325206279913862657525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76188401100159540600840133 14285325206279913862657525)
        ·
          refine ⟨1339249238088741924624143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14285325206279913862657525 1339249238088741924624143)
          ·
            refine ⟨2008873857133112886936215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339249238088741924624143 2008873857133112886936215)
            ·
              refine ⟨3013310785699669330404323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008873857133112886936215 3013310785699669330404323)
              ·
                refine ⟨4519966178549503995606485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013310785699669330404323 4519966178549503995606485)
                ·
                  refine ⟨105936707309753999897027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4519966178549503995606485 105936707309753999897027)
                  ·
                    rfl

theorem cell23_1856799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 7].length) (baseStart_1856799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856799 prefixEnd_1856799 := by exact prefixLift 1856799
  have htrace : WordTrace (prefixWord ++ tailWord_1856799) baseStart_1856799 baseEnd_1856799 := by
    simpa [prefixWord, tailWord_1856799, baseEnd_1856799] using wordTrace_append hprefix tailTrace_1856799
  have hstable : (prefixWord ++ tailWord_1856799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856799).length < 2 ^ (prefixWord ++ tailWord_1856799).sum := by decide
  have hdescent : baseEnd_1856799 < baseStart_1856799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856805 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_1856805 : Nat := 118140960795 + 1856805 * 2 ^ 59
def prefixEnd_1856805 : Nat := 4983230072969 + 3 ^ 40 * 1856805 * 2
def baseEnd_1856805 : Nat := 953433446671712975598215

theorem tailTrace_1856805 : CollatzResearch.WordTrace tailWord_1856805 prefixEnd_1856805 953433446671712975598215 := by
  unfold tailWord_1856805
  simp only [CollatzResearch.WordTrace]
  refine ⟨67723242038120076892131869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45148828025413384594754579 67723242038120076892131869)
  ·
    refine ⟨25396215764295028834549451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67723242038120076892131869 25396215764295028834549451)
    ·
      refine ⟨38094323646442543251824177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25396215764295028834549451 38094323646442543251824177)
      ·
        refine ⟨28570742734831907438868133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38094323646442543251824177 28570742734831907438868133)
        ·
          refine ⟨5357014262780982644787775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28570742734831907438868133 5357014262780982644787775)
          ·
            refine ⟨8035521394171473967181663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357014262780982644787775 8035521394171473967181663)
            ·
              refine ⟨12053282091257210950772495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035521394171473967181663 12053282091257210950772495)
              ·
                refine ⟨18079923136885816426158743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12053282091257210950772495 18079923136885816426158743)
                ·
                  refine ⟨27119884705328724639238115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18079923136885816426158743 27119884705328724639238115)
                  ·
                    refine ⟨40679827057993086958857173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27119884705328724639238115 40679827057993086958857173)
                    ·
                      refine ⟨953433446671712975598215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40679827057993086958857173 953433446671712975598215)
                      ·
                        rfl

theorem cell23_1856805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_1856805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856805 prefixEnd_1856805 := by exact prefixLift 1856805
  have htrace : WordTrace (prefixWord ++ tailWord_1856805) baseStart_1856805 baseEnd_1856805 := by
    simpa [prefixWord, tailWord_1856805, baseEnd_1856805] using wordTrace_append hprefix tailTrace_1856805
  have hstable : (prefixWord ++ tailWord_1856805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856805).length < 2 ^ (prefixWord ++ tailWord_1856805).sum := by decide
  have hdescent : baseEnd_1856805 < baseStart_1856805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856810 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1856810 : Nat := 118140960795 + 1856810 * 2 ^ 59
def prefixEnd_1856810 : Nat := 4983230072969 + 3 ^ 40 * 1856810 * 2
def baseEnd_1856810 : Nat := 953436014074985456035693

theorem tailTrace_1856810 : CollatzResearch.WordTrace tailWord_1856810 prefixEnd_1856810 953436014074985456035693 := by
  unfold tailWord_1856810
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930856100775490686515971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45148949602067975164042589 16930856100775490686515971)
  ·
    refine ⟨25396284151163236029773957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16930856100775490686515971 25396284151163236029773957)
    ·
      refine ⟨4761803278343106755582617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25396284151163236029773957 4761803278343106755582617)
      ·
        refine ⟨3571352458757330066686963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761803278343106755582617 3571352458757330066686963)
        ·
          refine ⟨5357028688135995100030445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571352458757330066686963 5357028688135995100030445)
          ·
            refine ⟨2008885758050998162511417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5357028688135995100030445 2008885758050998162511417)
            ·
              refine ⟨1506664318538248621883563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008885758050998162511417 1506664318538248621883563)
              ·
                refine ⟨2259996477807372932825345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506664318538248621883563 2259996477807372932825345)
                ·
                  refine ⟨1694997358355529699619009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2259996477807372932825345 1694997358355529699619009)
                  ·
                    refine ⟨1271248018766647274714257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694997358355529699619009 1271248018766647274714257)
                    ·
                      refine ⟨953436014074985456035693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271248018766647274714257 953436014074985456035693)
                      ·
                        rfl

theorem cell23_1856810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1856810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856810 prefixEnd_1856810 := by exact prefixLift 1856810
  have htrace : WordTrace (prefixWord ++ tailWord_1856810) baseStart_1856810 baseEnd_1856810 := by
    simpa [prefixWord, tailWord_1856810, baseEnd_1856810] using wordTrace_append hprefix tailTrace_1856810
  have hstable : (prefixWord ++ tailWord_1856810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856810).length < 2 ^ (prefixWord ++ tailWord_1856810).sum := by decide
  have hdescent : baseEnd_1856810 < baseStart_1856810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856815 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_1856815 : Nat := 118140960795 + 1856815 * 2 ^ 59
def prefixEnd_1856815 : Nat := 4983230072969 + 3 ^ 40 * 1856815 * 2
def baseEnd_1856815 : Nat := 953438581478257936473169

theorem tailTrace_1856815 : CollatzResearch.WordTrace tailWord_1856815 prefixEnd_1856815 953438581478257936473169 := by
  unfold tailWord_1856815
  simp only [CollatzResearch.WordTrace]
  refine ⟨67723606768083848599995899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45149071178722565733330599 67723606768083848599995899)
  ·
    refine ⟨101585410152125772899993849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67723606768083848599995899 101585410152125772899993849)
    ·
      refine ⟨76189057614094329674995387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101585410152125772899993849 76189057614094329674995387)
      ·
        refine ⟨114283586421141494512493081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76189057614094329674995387 114283586421141494512493081)
        ·
          refine ⟨85712689815856120884369811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114283586421141494512493081 85712689815856120884369811)
          ·
            refine ⟨128569034723784181326554717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85712689815856120884369811 128569034723784181326554717)
            ·
              refine ⟨48213388021419067997458019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128569034723784181326554717 48213388021419067997458019)
              ·
                refine ⟨72320082032128601996187029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48213388021419067997458019 72320082032128601996187029)
                ·
                  refine ⟨3390003845256028218571267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72320082032128601996187029 3390003845256028218571267)
                  ·
                    refine ⟨5085005767884042327856901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3390003845256028218571267 5085005767884042327856901)
                    ·
                      refine ⟨953438581478257936473169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5085005767884042327856901 953438581478257936473169)
                      ·
                        rfl

theorem cell23_1856815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_1856815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856815 prefixEnd_1856815 := by exact prefixLift 1856815
  have htrace : WordTrace (prefixWord ++ tailWord_1856815) baseStart_1856815 baseEnd_1856815 := by
    simpa [prefixWord, tailWord_1856815, baseEnd_1856815] using wordTrace_append hprefix tailTrace_1856815
  have hstable : (prefixWord ++ tailWord_1856815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856815).length < 2 ^ (prefixWord ++ tailWord_1856815).sum := by decide
  have hdescent : baseEnd_1856815 < baseStart_1856815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856832 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4]
def baseStart_1856832 : Nat := 118140960795 + 1856832 * 2 ^ 59
def prefixEnd_1856832 : Nat := 4983230072969 + 3 ^ 40 * 1856832 * 2
def baseEnd_1856832 : Nat := 953447310649384369960591

theorem tailTrace_1856832 : CollatzResearch.WordTrace tailWord_1856832 prefixEnd_1856832 953447310649384369960591 := by
  unfold tailWord_1856832
  simp only [CollatzResearch.WordTrace]
  refine ⟨33862113404511130251682375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45149484539348173668909833 33862113404511130251682375)
  ·
    refine ⟨50793170106766695377523563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33862113404511130251682375 50793170106766695377523563)
    ·
      refine ⟨76189755160150043066285345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50793170106766695377523563 76189755160150043066285345)
      ·
        refine ⟨57142316370112532299714009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76189755160150043066285345 57142316370112532299714009)
        ·
          refine ⟨42856737277584399224785507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57142316370112532299714009 42856737277584399224785507)
          ·
            refine ⟨64285105916376598837178261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42856737277584399224785507 64285105916376598837178261)
            ·
              refine ⟨3013364339830153070492731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64285105916376598837178261 3013364339830153070492731)
              ·
                refine ⟨4520046509745229605739097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013364339830153070492731 4520046509745229605739097)
                ·
                  refine ⟨3390034882308922204304323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4520046509745229605739097 3390034882308922204304323)
                  ·
                    refine ⟨5085052323463383306456485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3390034882308922204304323 5085052323463383306456485)
                    ·
                      refine ⟨953447310649384369960591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5085052323463383306456485 953447310649384369960591)
                      ·
                        rfl

theorem cell23_1856832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_1856832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856832 prefixEnd_1856832 := by exact prefixLift 1856832
  have htrace : WordTrace (prefixWord ++ tailWord_1856832) baseStart_1856832 baseEnd_1856832 := by
    simpa [prefixWord, tailWord_1856832, baseEnd_1856832] using wordTrace_append hprefix tailTrace_1856832
  have hstable : (prefixWord ++ tailWord_1856832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856832).length < 2 ^ (prefixWord ++ tailWord_1856832).sum := by decide
  have hdescent : baseEnd_1856832 < baseStart_1856832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856916 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1856916 : Nat := 118140960795 + 1856916 * 2 ^ 59
def prefixEnd_1856916 : Nat := 4983230072969 + 3 ^ 40 * 1856916 * 2
def baseEnd_1856916 : Nat := 953490443024362041310205

theorem tailTrace_1856916 : CollatzResearch.WordTrace tailWord_1856916 prefixEnd_1856916 953490443024362041310205 := by
  unfold tailWord_1856916
  simp only [CollatzResearch.WordTrace]
  refine ⟨33863645270358971424711301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45151527027145295232948401 33863645270358971424711301)
  ·
    refine ⟨6349433488192307142133369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33863645270358971424711301 6349433488192307142133369)
    ·
      refine ⟨4762075116144230356600027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6349433488192307142133369 4762075116144230356600027)
      ·
        refine ⟨7143112674216345534900041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4762075116144230356600027 7143112674216345534900041)
        ·
          refine ⟨5357334505662259151175031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7143112674216345534900041 5357334505662259151175031)
          ·
            refine ⟨8036001758493388726762547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357334505662259151175031 8036001758493388726762547)
            ·
              refine ⟨12054002637740083090143821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036001758493388726762547 12054002637740083090143821)
              ·
                refine ⟨4520250989152531158803933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12054002637740083090143821 4520250989152531158803933)
                ·
                  refine ⟨1695094120932199184551475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4520250989152531158803933 1695094120932199184551475)
                  ·
                    refine ⟨2542641181398298776827213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1695094120932199184551475 2542641181398298776827213)
                    ·
                      refine ⟨953490443024362041310205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2542641181398298776827213 953490443024362041310205)
                      ·
                        rfl

theorem cell23_1856916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1856916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856916 prefixEnd_1856916 := by exact prefixLift 1856916
  have htrace : WordTrace (prefixWord ++ tailWord_1856916) baseStart_1856916 baseEnd_1856916 := by
    simpa [prefixWord, tailWord_1856916, baseEnd_1856916] using wordTrace_append hprefix tailTrace_1856916
  have hstable : (prefixWord ++ tailWord_1856916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856916).length < 2 ^ (prefixWord ++ tailWord_1856916).sum := by decide
  have hdescent : baseEnd_1856916 < baseStart_1856916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856939 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 9, 2, 2]
def baseStart_1856939 : Nat := 118140960795 + 1856939 * 2 ^ 59
def prefixEnd_1856939 : Nat := 4983230072969 + 3 ^ 40 * 1856939 * 2
def baseEnd_1856939 : Nat := 953502253079415451322599

theorem tailTrace_1856939 : CollatzResearch.WordTrace tailWord_1856939 prefixEnd_1856939 953502253079415451322599 := by
  unfold tailWord_1856939
  simp only [CollatzResearch.WordTrace]
  refine ⟨67728129419634617777509871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45152086279756411851673247 67728129419634617777509871)
  ·
    refine ⟨101592194129451926666264807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67728129419634617777509871 101592194129451926666264807)
    ·
      refine ⟨152388291194177889999397211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101592194129451926666264807 152388291194177889999397211)
      ·
        refine ⟨228582436791266834999095817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152388291194177889999397211 228582436791266834999095817)
        ·
          refine ⟨171436827593450126249321863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228582436791266834999095817 171436827593450126249321863)
          ·
            refine ⟨257155241390175189373982795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171436827593450126249321863 257155241390175189373982795)
            ·
              refine ⟨385732862085262784060974193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257155241390175189373982795 385732862085262784060974193)
              ·
                refine ⟨289299646563947088045730645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385732862085262784060974193 289299646563947088045730645)
                ·
                  refine ⟨1695115116585627469017953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 289299646563947088045730645 1695115116585627469017953)
                  ·
                    refine ⟨1271336337439220601763465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1695115116585627469017953 1271336337439220601763465)
                    ·
                      refine ⟨953502253079415451322599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271336337439220601763465 953502253079415451322599)
                      ·
                        rfl

theorem cell23_1856939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 2, 2].length) (baseStart_1856939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856939 prefixEnd_1856939 := by exact prefixLift 1856939
  have htrace : WordTrace (prefixWord ++ tailWord_1856939) baseStart_1856939 baseEnd_1856939 := by
    simpa [prefixWord, tailWord_1856939, baseEnd_1856939] using wordTrace_append hprefix tailTrace_1856939
  have hstable : (prefixWord ++ tailWord_1856939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856939).length < 2 ^ (prefixWord ++ tailWord_1856939).sum := by decide
  have hdescent : baseEnd_1856939 < baseStart_1856939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856949 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_1856949 : Nat := 118140960795 + 1856949 * 2 ^ 59
def prefixEnd_1856949 : Nat := 4983230072969 + 3 ^ 40 * 1856949 * 2
def baseEnd_1856949 : Nat := 317835795961986804065851

theorem tailTrace_1856949 : CollatzResearch.WordTrace tailWord_1856949 prefixEnd_1856949 317835795961986804065851 := by
  unfold tailWord_1856949
  simp only [CollatzResearch.WordTrace]
  refine ⟨67728494149598389485373901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45152329433065592990249267 67728494149598389485373901)
  ·
    refine ⟨25398185306099396057015213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67728494149598389485373901 25398185306099396057015213)
    ·
      refine ⟨9524319489787273521380705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25398185306099396057015213 9524319489787273521380705)
      ·
        refine ⟨7143239617340455141035529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9524319489787273521380705 7143239617340455141035529)
        ·
          refine ⟨5357429713005341355776647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7143239617340455141035529 5357429713005341355776647)
          ·
            refine ⟨8036144569508012033664971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357429713005341355776647 8036144569508012033664971)
            ·
              refine ⟨12054216854262018050497457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036144569508012033664971 12054216854262018050497457)
              ·
                refine ⟨9040662640696513537873093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12054216854262018050497457 9040662640696513537873093)
                ·
                  refine ⟨1695124245130596288351205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9040662640696513537873093 1695124245130596288351205)
                  ·
                    refine ⟨317835795961986804065851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695124245130596288351205 317835795961986804065851)
                    ·
                      rfl

theorem cell23_1856949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_1856949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856949 prefixEnd_1856949 := by exact prefixLift 1856949
  have htrace : WordTrace (prefixWord ++ tailWord_1856949) baseStart_1856949 baseEnd_1856949 := by
    simpa [prefixWord, tailWord_1856949, baseEnd_1856949] using wordTrace_append hprefix tailTrace_1856949
  have hstable : (prefixWord ++ tailWord_1856949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856949).length < 2 ^ (prefixWord ++ tailWord_1856949).sum := by decide
  have hdescent : baseEnd_1856949 < baseStart_1856949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856952 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_1856952 : Nat := 118140960795 + 1856952 * 2 ^ 59
def prefixEnd_1856952 : Nat := 4983230072969 + 3 ^ 40 * 1856952 * 2
def baseEnd_1856952 : Nat := 953508928327923900460039

theorem tailTrace_1856952 : CollatzResearch.WordTrace tailWord_1856952 prefixEnd_1856952 953508928327923900460039 := by
  unfold tailWord_1856952
  simp only [CollatzResearch.WordTrace]
  refine ⟨33864301784293760498866555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45152402379058347331822073 33864301784293760498866555)
  ·
    refine ⟨50796452676440640748299833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33864301784293760498866555 50796452676440640748299833)
    ·
      refine ⟨38097339507330480561224875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50796452676440640748299833 38097339507330480561224875)
      ·
        refine ⟨57146009260995720841837313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38097339507330480561224875 57146009260995720841837313)
        ·
          refine ⟨42859506945746790631377985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57146009260995720841837313 42859506945746790631377985)
          ·
            refine ⟨32144630209310092973533489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42859506945746790631377985 32144630209310092973533489)
            ·
              refine ⟨24108472656982569730150117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32144630209310092973533489 24108472656982569730150117)
              ·
                refine ⟨4520338623184231824403147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24108472656982569730150117 4520338623184231824403147)
                ·
                  refine ⟨6780507934776347736604721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520338623184231824403147 6780507934776347736604721)
                  ·
                    refine ⟨5085380951082260802453541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6780507934776347736604721 5085380951082260802453541)
                    ·
                      refine ⟨953508928327923900460039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5085380951082260802453541 953508928327923900460039)
                      ·
                        rfl

theorem cell23_1856952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_1856952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1856952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1856952 prefixEnd_1856952 := by exact prefixLift 1856952
  have htrace : WordTrace (prefixWord ++ tailWord_1856952) baseStart_1856952 baseEnd_1856952 := by
    simpa [prefixWord, tailWord_1856952, baseEnd_1856952] using wordTrace_append hprefix tailTrace_1856952
  have hstable : (prefixWord ++ tailWord_1856952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856952).length < 2 ^ (prefixWord ++ tailWord_1856952).sum := by decide
  have hdescent : baseEnd_1856952 < baseStart_1856952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857029 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 5, 4, 2]
def baseStart_1857029 : Nat := 118140960795 + 1857029 * 2 ^ 59
def prefixEnd_1857029 : Nat := 4983230072969 + 3 ^ 40 * 1857029 * 2
def baseEnd_1857029 : Nat := 953548466338320099197185

theorem tailTrace_1857029 : CollatzResearch.WordTrace tailWord_1857029 prefixEnd_1857029 953548466338320099197185 := by
  unfold tailWord_1857029
  simp only [CollatzResearch.WordTrace]
  refine ⟨67731411989308563148286141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45154274659539042098857427 67731411989308563148286141)
  ·
    refine ⟨25399279495990711180607303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67731411989308563148286141 25399279495990711180607303)
    ·
      refine ⟨38098919243986066770910955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25399279495990711180607303 38098919243986066770910955)
      ·
        refine ⟨57148378865979100156366433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38098919243986066770910955 57148378865979100156366433)
        ·
          refine ⟨42861284149484325117274825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57148378865979100156366433 42861284149484325117274825)
          ·
            refine ⟨32145963112113243837956119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42861284149484325117274825 32145963112113243837956119)
            ·
              refine ⟨48218944668169865756934179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32145963112113243837956119 48218944668169865756934179)
              ·
                refine ⟨72328417002254798635401269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48218944668169865756934179 72328417002254798635401269)
                ·
                  refine ⟨6780789093961387372068869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72328417002254798635401269 6780789093961387372068869)
                  ·
                    refine ⟨1271397955117760132262913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6780789093961387372068869 1271397955117760132262913)
                    ·
                      refine ⟨953548466338320099197185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271397955117760132262913 953548466338320099197185)
                      ·
                        rfl

theorem cell23_1857029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_1857029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857029 prefixEnd_1857029 := by exact prefixLift 1857029
  have htrace : WordTrace (prefixWord ++ tailWord_1857029) baseStart_1857029 baseEnd_1857029 := by
    simpa [prefixWord, tailWord_1857029, baseEnd_1857029] using wordTrace_append hprefix tailTrace_1857029
  have hstable : (prefixWord ++ tailWord_1857029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857029).length < 2 ^ (prefixWord ++ tailWord_1857029).sum := by decide
  have hdescent : baseEnd_1857029 < baseStart_1857029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857030 : List Nat := [6, 2, 1, 1, 2, 2, 1, 8]
def baseStart_1857030 : Nat := 118140960795 + 1857030 * 2 ^ 59
def prefixEnd_1857030 : Nat := 4983230072969 + 3 ^ 40 * 1857030 * 2
def baseEnd_1857030 : Nat := 35316628882184244269803

theorem tailTrace_1857030 : CollatzResearch.WordTrace tailWord_1857030 prefixEnd_1857030 35316628882184244269803 := by
  unfold tailWord_1857030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116607764447029384971017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45154298974869960212715029 2116607764447029384971017)
  ·
    refine ⟨1587455823335272038728263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2116607764447029384971017 1587455823335272038728263)
    ·
      refine ⟨2381183735002908058092395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587455823335272038728263 2381183735002908058092395)
      ·
        refine ⟨3571775602504362087138593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381183735002908058092395 3571775602504362087138593)
        ·
          refine ⟨2678831701878271565353945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571775602504362087138593 2678831701878271565353945)
          ·
            refine ⟨2009123776408703674015459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678831701878271565353945 2009123776408703674015459)
            ·
              refine ⟨3013685664613055511023189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009123776408703674015459 3013685664613055511023189)
              ·
                refine ⟨35316628882184244269803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3013685664613055511023189 35316628882184244269803)
                ·
                  rfl

theorem cell23_1857030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_1857030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857030 prefixEnd_1857030 := by exact prefixLift 1857030
  have htrace : WordTrace (prefixWord ++ tailWord_1857030) baseStart_1857030 baseEnd_1857030 := by
    simpa [prefixWord, tailWord_1857030, baseEnd_1857030] using wordTrace_append hprefix tailTrace_1857030
  have hstable : (prefixWord ++ tailWord_1857030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857030).length < 2 ^ (prefixWord ++ tailWord_1857030).sum := by decide
  have hdescent : baseEnd_1857030 < baseStart_1857030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857032 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1857032 : Nat := 118140960795 + 1857032 * 2 ^ 59
def prefixEnd_1857032 : Nat := 4983230072969 + 3 ^ 40 * 1857032 * 2
def baseEnd_1857032 : Nat := 953550006780283587459671

theorem tailTrace_1857032 : CollatzResearch.WordTrace tailWord_1857032 prefixEnd_1857032 953550006780283587459671 := by
  unfold tailWord_1857032
  simp only [CollatzResearch.WordTrace]
  refine ⟨33865760704148847330322675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45154347605531796440430233 33865760704148847330322675)
  ·
    refine ⟨50798641056223270995484013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33865760704148847330322675 50798641056223270995484013)
    ·
      refine ⟨19049490396083726623306505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50798641056223270995484013 19049490396083726623306505)
      ·
        refine ⟨14287117797062794967479879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19049490396083726623306505 14287117797062794967479879)
        ·
          refine ⟨21430676695594192451219819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14287117797062794967479879 21430676695594192451219819)
          ·
            refine ⟨32146015043391288676829729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21430676695594192451219819 32146015043391288676829729)
            ·
              refine ⟨24109511282543466507622297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32146015043391288676829729 24109511282543466507622297)
              ·
                refine ⟨18082133461907599880716723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24109511282543466507622297 18082133461907599880716723)
                ·
                  refine ⟨27123200192861399821075085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18082133461907599880716723 27123200192861399821075085)
                  ·
                    refine ⟨10171200072323024932903157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27123200192861399821075085 10171200072323024932903157)
                    ·
                      refine ⟨953550006780283587459671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10171200072323024932903157 953550006780283587459671)
                      ·
                        rfl

theorem cell23_1857032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1857032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857032 prefixEnd_1857032 := by exact prefixLift 1857032
  have htrace : WordTrace (prefixWord ++ tailWord_1857032) baseStart_1857032 baseEnd_1857032 := by
    simpa [prefixWord, tailWord_1857032, baseEnd_1857032] using wordTrace_append hprefix tailTrace_1857032
  have hstable : (prefixWord ++ tailWord_1857032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857032).length < 2 ^ (prefixWord ++ tailWord_1857032).sum := by decide
  have hdescent : baseEnd_1857032 < baseStart_1857032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857079 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 3]
def baseStart_1857079 : Nat := 118140960795 + 1857079 * 2 ^ 59
def prefixEnd_1857079 : Nat := 4983230072969 + 3 ^ 40 * 1857079 * 2
def baseEnd_1857079 : Nat := 953574140371044903571955

theorem tailTrace_1857079 : CollatzResearch.WordTrace tailWord_1857079 prefixEnd_1857079 953574140371044903571955 := by
  unfold tailWord_1857079
  simp only [CollatzResearch.WordTrace]
  refine ⟨67733235639127421687606291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45155490426084947791737527 67733235639127421687606291)
  ·
    refine ⟨101599853458691132531409437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67733235639127421687606291 101599853458691132531409437)
    ·
      refine ⟨38099945047009174699278539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101599853458691132531409437 38099945047009174699278539)
      ·
        refine ⟨57149917570513762048917809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38099945047009174699278539 57149917570513762048917809)
        ·
          refine ⟨42862438177885321536688357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57149917570513762048917809 42862438177885321536688357)
          ·
            refine ⟨8036707158353497788129067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42862438177885321536688357 8036707158353497788129067)
            ·
              refine ⟨12055060737530246682193601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036707158353497788129067 12055060737530246682193601)
              ·
                refine ⟨9041295553147685011645201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12055060737530246682193601 9041295553147685011645201)
                ·
                  refine ⟨6780971664860763758733901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9041295553147685011645201 6780971664860763758733901)
                  ·
                    refine ⟨2542864374322786409525213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6780971664860763758733901 2542864374322786409525213)
                    ·
                      refine ⟨953574140371044903571955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2542864374322786409525213 953574140371044903571955)
                      ·
                        rfl

theorem cell23_1857079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_1857079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857079 prefixEnd_1857079 := by exact prefixLift 1857079
  have htrace : WordTrace (prefixWord ++ tailWord_1857079) baseStart_1857079 baseEnd_1857079 := by
    simpa [prefixWord, tailWord_1857079, baseEnd_1857079] using wordTrace_append hprefix tailTrace_1857079
  have hstable : (prefixWord ++ tailWord_1857079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857079).length < 2 ^ (prefixWord ++ tailWord_1857079).sum := by decide
  have hdescent : baseEnd_1857079 < baseStart_1857079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857080 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 2, 2, 2]
def baseStart_1857080 : Nat := 118140960795 + 1857080 * 2 ^ 59
def prefixEnd_1857080 : Nat := 4983230072969 + 3 ^ 40 * 1857080 * 2
def baseEnd_1857080 : Nat := 953574653851699399659451

theorem tailTrace_1857080 : CollatzResearch.WordTrace tailWord_1857080 prefixEnd_1857080 953574653851699399659451 := by
  unfold tailWord_1857080
  simp only [CollatzResearch.WordTrace]
  refine ⟨33866636056061899429196347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45155514741415865905595129 33866636056061899429196347)
  ·
    refine ⟨50799954084092849143794521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33866636056061899429196347 50799954084092849143794521)
    ·
      refine ⟨38099965563069636857845891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50799954084092849143794521 38099965563069636857845891)
      ·
        refine ⟨57149948344604455286768837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38099965563069636857845891 57149948344604455286768837)
        ·
          refine ⟨10715615314613335366269157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57149948344604455286768837 10715615314613335366269157)
          ·
            refine ⟨2009177871490000381175467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10715615314613335366269157 2009177871490000381175467)
            ·
              refine ⟨3013766807235000571763201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009177871490000381175467 3013766807235000571763201)
              ·
                refine ⟨2260325105426250428822401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013766807235000571763201 2260325105426250428822401)
                ·
                  refine ⟨1695243829069687821616801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2260325105426250428822401 1695243829069687821616801)
                  ·
                    refine ⟨1271432871802265866212601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1695243829069687821616801 1271432871802265866212601)
                    ·
                      refine ⟨953574653851699399659451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271432871802265866212601 953574653851699399659451)
                      ·
                        rfl

theorem cell23_1857080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_1857080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857080 prefixEnd_1857080 := by exact prefixLift 1857080
  have htrace : WordTrace (prefixWord ++ tailWord_1857080) baseStart_1857080 baseEnd_1857080 := by
    simpa [prefixWord, tailWord_1857080, baseEnd_1857080] using wordTrace_append hprefix tailTrace_1857080
  have hstable : (prefixWord ++ tailWord_1857080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857080).length < 2 ^ (prefixWord ++ tailWord_1857080).sum := by decide
  have hdescent : baseEnd_1857080 < baseStart_1857080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857112 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 10]
def baseStart_1857112 : Nat := 118140960795 + 1857112 * 2 ^ 59
def prefixEnd_1857112 : Nat := 4983230072969 + 3 ^ 40 * 1857112 * 2
def baseEnd_1857112 : Nat := 317863695077547758153101

theorem tailTrace_1857112 : CollatzResearch.WordTrace tailWord_1857112 prefixEnd_1857112 317863695077547758153101 := by
  unfold tailWord_1857112
  simp only [CollatzResearch.WordTrace]
  refine ⟨33867219624003934161778795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45156292832005245549038393 33867219624003934161778795)
  ·
    refine ⟨50800829436005901242668193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33867219624003934161778795 50800829436005901242668193)
    ·
      refine ⟨38100622077004425932001145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50800829436005901242668193 38100622077004425932001145)
      ·
        refine ⟨28575466557753319449000859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38100622077004425932001145 28575466557753319449000859)
        ·
          refine ⟨42863199836629979173501289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28575466557753319449000859 42863199836629979173501289)
          ·
            refine ⟨32147399877472484380125967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42863199836629979173501289 32147399877472484380125967)
            ·
              refine ⟨48221099816208726570188951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32147399877472484380125967 48221099816208726570188951)
              ·
                refine ⟨72331649724313089855283427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48221099816208726570188951 72331649724313089855283427)
                ·
                  refine ⟨108497474586469634782925141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72331649724313089855283427 108497474586469634782925141)
                  ·
                    refine ⟨317863695077547758153101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 108497474586469634782925141 317863695077547758153101)
                    ·
                      rfl

theorem cell23_1857112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_1857112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857112 prefixEnd_1857112 := by exact prefixLift 1857112
  have htrace : WordTrace (prefixWord ++ tailWord_1857112) baseStart_1857112 baseEnd_1857112 := by
    simpa [prefixWord, tailWord_1857112, baseEnd_1857112] using wordTrace_append hprefix tailTrace_1857112
  have hstable : (prefixWord ++ tailWord_1857112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857112).length < 2 ^ (prefixWord ++ tailWord_1857112).sum := by decide
  have hdescent : baseEnd_1857112 < baseStart_1857112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857129 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 5, 4]
def baseStart_1857129 : Nat := 118140960795 + 1857129 * 2 ^ 59
def prefixEnd_1857129 : Nat := 4983230072969 + 3 ^ 40 * 1857129 * 2
def baseEnd_1857129 : Nat := 317866604801256569315575

theorem tailTrace_1857129 : CollatzResearch.WordTrace tailWord_1857129 prefixEnd_1857129 317866604801256569315575 := by
  unfold tailWord_1857129
  simp only [CollatzResearch.WordTrace]
  refine ⟨67735059288946280226926441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45156706192630853484617627 67735059288946280226926441)
  ·
    refine ⟨50801294466709710170194831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67735059288946280226926441 50801294466709710170194831)
    ·
      refine ⟨76201941700064565255292247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50801294466709710170194831 76201941700064565255292247)
      ·
        refine ⟨114302912550096847882938371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76201941700064565255292247 114302912550096847882938371)
        ·
          refine ⟨171454368825145271824407557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114302912550096847882938371 171454368825145271824407557)
          ·
            refine ⟨32147694154714738467076417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171454368825145271824407557 32147694154714738467076417)
            ·
              refine ⟨24110770616036053850307313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32147694154714738467076417 24110770616036053850307313)
              ·
                refine ⟨18083077962027040387730485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24110770616036053850307313 18083077962027040387730485)
                ·
                  refine ⟨1695288558940035036349733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18083077962027040387730485 1695288558940035036349733)
                  ·
                    refine ⟨317866604801256569315575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1695288558940035036349733 317866604801256569315575)
                    ·
                      rfl

theorem cell23_1857129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 4].length) (baseStart_1857129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857129 prefixEnd_1857129 := by exact prefixLift 1857129
  have htrace : WordTrace (prefixWord ++ tailWord_1857129) baseStart_1857129 baseEnd_1857129 := by
    simpa [prefixWord, tailWord_1857129, baseEnd_1857129] using wordTrace_append hprefix tailTrace_1857129
  have hstable : (prefixWord ++ tailWord_1857129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857129).length < 2 ^ (prefixWord ++ tailWord_1857129).sum := by decide
  have hdescent : baseEnd_1857129 < baseStart_1857129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857136 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_1857136 : Nat := 118140960795 + 1857136 * 2 ^ 59
def prefixEnd_1857136 : Nat := 4983230072969 + 3 ^ 40 * 1857136 * 2
def baseEnd_1857136 : Nat := 953603408768351180559193

theorem tailTrace_1857136 : CollatzResearch.WordTrace tailWord_1857136 prefixEnd_1857136 953603408768351180559193 := by
  unfold tailWord_1857136
  simp only [CollatzResearch.WordTrace]
  refine ⟨33867657299960460211215631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45156876399947280281620841 33867657299960460211215631)
  ·
    refine ⟨50801485949940690316823447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33867657299960460211215631 50801485949940690316823447)
    ·
      refine ⟨76202228924911035475235171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50801485949940690316823447 76202228924911035475235171)
      ·
        refine ⟨114303343387366553212852757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76202228924911035475235171 114303343387366553212852757)
        ·
          refine ⟨5357969221282807181852473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114303343387366553212852757 5357969221282807181852473)
          ·
            refine ⟨4018476915962105386389355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5357969221282807181852473 4018476915962105386389355)
            ·
              refine ⟨6027715373943158079584033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018476915962105386389355 6027715373943158079584033)
              ·
                refine ⟨4520786530457368559688025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6027715373943158079584033 4520786530457368559688025)
                ·
                  refine ⟨3390589897843026419766019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4520786530457368559688025 3390589897843026419766019)
                  ·
                    refine ⟨5085884846764539629649029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3390589897843026419766019 5085884846764539629649029)
                    ·
                      refine ⟨953603408768351180559193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5085884846764539629649029 953603408768351180559193)
                      ·
                        rfl

theorem cell23_1857136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_1857136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857136 prefixEnd_1857136 := by exact prefixLift 1857136
  have htrace : WordTrace (prefixWord ++ tailWord_1857136) baseStart_1857136 baseEnd_1857136 := by
    simpa [prefixWord, tailWord_1857136, baseEnd_1857136] using wordTrace_append hprefix tailTrace_1857136
  have hstable : (prefixWord ++ tailWord_1857136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857136).length < 2 ^ (prefixWord ++ tailWord_1857136).sum := by decide
  have hdescent : baseEnd_1857136 < baseStart_1857136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857279 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 2, 7]
def baseStart_1857279 : Nat := 118140960795 + 1857279 * 2 ^ 59
def prefixEnd_1857279 : Nat := 4983230072969 + 3 ^ 40 * 1857279 * 2
def baseEnd_1857279 : Nat := 317892278833981373690345

theorem tailTrace_1857279 : CollatzResearch.WordTrace tailWord_1857279 prefixEnd_1857279 317892278833981373690345 := by
  unfold tailWord_1857279
  simp only [CollatzResearch.WordTrace]
  refine ⟨67740530238402855844886891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45160353492268570563257927 67740530238402855844886891)
  ·
    refine ⟨101610795357604283767330337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67740530238402855844886891 101610795357604283767330337)
    ·
      refine ⟨76208096518203212825497753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101610795357604283767330337 76208096518203212825497753)
      ·
        refine ⟨57156072388652409619123315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76208096518203212825497753 57156072388652409619123315)
        ·
          refine ⟨85734108582978614428684973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57156072388652409619123315 85734108582978614428684973)
          ·
            refine ⟨32150290718616980410756865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85734108582978614428684973 32150290718616980410756865)
            ·
              refine ⟨24112718038962735308067649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32150290718616980410756865 24112718038962735308067649)
              ·
                refine ⟨18084538529222051481050737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24112718038962735308067649 18084538529222051481050737)
                ·
                  refine ⟨13563403896916538610788053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18084538529222051481050737 13563403896916538610788053)
                  ·
                    refine ⟨317892278833981373690345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13563403896916538610788053 317892278833981373690345)
                    ·
                      rfl

theorem cell23_1857279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_1857279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857279 prefixEnd_1857279 := by exact prefixLift 1857279
  have htrace : WordTrace (prefixWord ++ tailWord_1857279) baseStart_1857279 baseEnd_1857279 := by
    simpa [prefixWord, tailWord_1857279, baseEnd_1857279] using wordTrace_append hprefix tailTrace_1857279
  have hstable : (prefixWord ++ tailWord_1857279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857279).length < 2 ^ (prefixWord ++ tailWord_1857279).sum := by decide
  have hdescent : baseEnd_1857279 < baseStart_1857279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857336 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1857336 : Nat := 118140960795 + 1857336 * 2 ^ 59
def prefixEnd_1857336 : Nat := 4983230072969 + 3 ^ 40 * 1857336 * 2
def baseEnd_1857336 : Nat := 953706104899250398058273

theorem tailTrace_1857336 : CollatzResearch.WordTrace tailWord_1857336 prefixEnd_1857336 953706104899250398058273 := by
  unfold tailWord_1857336
  simp only [CollatzResearch.WordTrace]
  refine ⟨33871304599598177289855931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45161739466130903053141241 33871304599598177289855931)
  ·
    refine ⟨50806956899397265934783897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33871304599598177289855931 50806956899397265934783897)
    ·
      refine ⟨38105217674547949451087923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50806956899397265934783897 38105217674547949451087923)
      ·
        refine ⟨57157826511821924176631885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38105217674547949451087923 57157826511821924176631885)
        ·
          refine ⟨21434184941933221566236957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57157826511821924176631885 21434184941933221566236957)
          ·
            refine ⟨8037819353224958087338859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21434184941933221566236957 8037819353224958087338859)
            ·
              refine ⟨12056729029837437131008289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8037819353224958087338859 12056729029837437131008289)
              ·
                refine ⟨9042546772378077848256217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12056729029837437131008289 9042546772378077848256217)
                ·
                  refine ⟨6781910079283558386192163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9042546772378077848256217 6781910079283558386192163)
                  ·
                    refine ⟨10172865118925337579288245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781910079283558386192163 10172865118925337579288245)
                    ·
                      refine ⟨953706104899250398058273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10172865118925337579288245 953706104899250398058273)
                      ·
                        rfl

theorem cell23_1857336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1857336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857336 prefixEnd_1857336 := by exact prefixLift 1857336
  have htrace : WordTrace (prefixWord ++ tailWord_1857336) baseStart_1857336 baseEnd_1857336 := by
    simpa [prefixWord, tailWord_1857336, baseEnd_1857336] using wordTrace_append hprefix tailTrace_1857336
  have hstable : (prefixWord ++ tailWord_1857336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857336).length < 2 ^ (prefixWord ++ tailWord_1857336).sum := by decide
  have hdescent : baseEnd_1857336 < baseStart_1857336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857337 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 3, 3, 2]
def baseStart_1857337 : Nat := 118140960795 + 1857337 * 2 ^ 59
def prefixEnd_1857337 : Nat := 4983230072969 + 3 ^ 40 * 1857337 * 2
def baseEnd_1857337 : Nat := 953706618379904894145769

theorem tailTrace_1857337 : CollatzResearch.WordTrace tailWord_1857337 prefixEnd_1857337 953706618379904894145769 := by
  unfold tailWord_1857337
  simp only [CollatzResearch.WordTrace]
  refine ⟨67742645672192731750498265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45161763781461821166998843 67742645672192731750498265)
  ·
    refine ⟨50806984254144548812873699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67742645672192731750498265 50806984254144548812873699)
    ·
      refine ⟨76210476381216823219310549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50806984254144548812873699 76210476381216823219310549)
      ·
        refine ⟨1786183040184769294202591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 76210476381216823219310549 1786183040184769294202591)
        ·
          refine ⟨2679274560277153941303887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786183040184769294202591 2679274560277153941303887)
          ·
            refine ⟨4018911840415730911955831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679274560277153941303887 4018911840415730911955831)
            ·
              refine ⟨6028367760623596367933747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018911840415730911955831 6028367760623596367933747)
              ·
                refine ⟨9042551640935394551900621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028367760623596367933747 9042551640935394551900621)
                ·
                  refine ⟨3390956865350772956962733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9042551640935394551900621 3390956865350772956962733)
                  ·
                    refine ⟨1271608824506539858861025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3390956865350772956962733 1271608824506539858861025)
                    ·
                      refine ⟨953706618379904894145769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271608824506539858861025 953706618379904894145769)
                      ·
                        rfl

theorem cell23_1857337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_1857337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857337 prefixEnd_1857337 := by exact prefixLift 1857337
  have htrace : WordTrace (prefixWord ++ tailWord_1857337) baseStart_1857337 baseEnd_1857337 := by
    simpa [prefixWord, tailWord_1857337, baseEnd_1857337] using wordTrace_append hprefix tailTrace_1857337
  have hstable : (prefixWord ++ tailWord_1857337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857337).length < 2 ^ (prefixWord ++ tailWord_1857337).sum := by decide
  have hdescent : baseEnd_1857337 < baseStart_1857337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857383 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1857383 : Nat := 118140960795 + 1857383 * 2 ^ 59
def prefixEnd_1857383 : Nat := 4983230072969 + 3 ^ 40 * 1857383 * 2
def baseEnd_1857383 : Nat := 953730238490011714170557

theorem tailTrace_1857383 : CollatzResearch.WordTrace tailWord_1857383 prefixEnd_1857383 953730238490011714170557 := by
  unfold tailWord_1857383
  simp only [CollatzResearch.WordTrace]
  refine ⟨67744323430026081606672803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45162882286684054404448535 67744323430026081606672803)
  ·
    refine ⟨101616485145039122410009205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67744323430026081606672803 101616485145039122410009205)
    ·
      refine ⟨9526545482347417725938363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101616485145039122410009205 9526545482347417725938363)
      ·
        refine ⟨14289818223521126588907545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9526545482347417725938363 14289818223521126588907545)
        ·
          refine ⟨10717363667640844941680659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14289818223521126588907545 10717363667640844941680659)
          ·
            refine ⟨16076045501461267412520989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10717363667640844941680659 16076045501461267412520989)
            ·
              refine ⟨6028517063047975279695371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16076045501461267412520989 6028517063047975279695371)
              ·
                refine ⟨9042775594571962919543057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028517063047975279695371 9042775594571962919543057)
                ·
                  refine ⟨6782081695928972189657293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9042775594571962919543057 6782081695928972189657293)
                  ·
                    refine ⟨2543280635973364571121485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6782081695928972189657293 2543280635973364571121485)
                    ·
                      refine ⟨953730238490011714170557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2543280635973364571121485 953730238490011714170557)
                      ·
                        rfl

theorem cell23_1857383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1857383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857383 prefixEnd_1857383 := by exact prefixLift 1857383
  have htrace : WordTrace (prefixWord ++ tailWord_1857383) baseStart_1857383 baseEnd_1857383 := by
    simpa [prefixWord, tailWord_1857383, baseEnd_1857383] using wordTrace_append hprefix tailTrace_1857383
  have hstable : (prefixWord ++ tailWord_1857383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857383).length < 2 ^ (prefixWord ++ tailWord_1857383).sum := by decide
  have hdescent : baseEnd_1857383 < baseStart_1857383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857393 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 2, 5, 2]
def baseStart_1857393 : Nat := 118140960795 + 1857393 * 2 ^ 59
def prefixEnd_1857393 : Nat := 4983230072969 + 3 ^ 40 * 1857393 * 2
def baseEnd_1857393 : Nat := 953735373296556675045511

theorem tailTrace_1857393 : CollatzResearch.WordTrace tailWord_1857393 prefixEnd_1857393 953735373296556675045511 := by
  unfold tailWord_1857393
  simp only [CollatzResearch.WordTrace]
  refine ⟨67744688159989853314536833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45163125439993235543024555 67744688159989853314536833)
  ·
    refine ⟨50808516119992389985902625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67744688159989853314536833 50808516119992389985902625)
    ·
      refine ⟨38106387089994292489426969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50808516119992389985902625 38106387089994292489426969)
      ·
        refine ⟨28579790317495719367070227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38106387089994292489426969 28579790317495719367070227)
        ·
          refine ⟨42869685476243579050605341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28579790317495719367070227 42869685476243579050605341)
          ·
            refine ⟨16076132053591342143977003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42869685476243579050605341 16076132053591342143977003)
            ·
              refine ⟨24114198080387013215965505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16076132053591342143977003 24114198080387013215965505)
              ·
                refine ⟨18085648560290259911974129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24114198080387013215965505 18085648560290259911974129)
                ·
                  refine ⟨13564236420217694933980597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18085648560290259911974129 13564236420217694933980597)
                  ·
                    refine ⟨1271647164395408900060681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13564236420217694933980597 1271647164395408900060681)
                    ·
                      refine ⟨953735373296556675045511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1271647164395408900060681 953735373296556675045511)
                      ·
                        rfl

theorem cell23_1857393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_1857393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1857393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1857393 prefixEnd_1857393 := by exact prefixLift 1857393
  have htrace : WordTrace (prefixWord ++ tailWord_1857393) baseStart_1857393 baseEnd_1857393 := by
    simpa [prefixWord, tailWord_1857393, baseEnd_1857393] using wordTrace_append hprefix tailTrace_1857393
  have hstable : (prefixWord ++ tailWord_1857393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857393).length < 2 ^ (prefixWord ++ tailWord_1857393).sum := by decide
  have hdescent : baseEnd_1857393 < baseStart_1857393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
